// =============================================================================
//  voicefx.cpp  -  AML mod "VoiceFX" v3.0
//  Voice changer realtime untuk voice chat SA-MP Android.
//
//  Cara kerja:
//   1. Hook BASS_RecordStart (libBASS.so) memakai Dobby (libdobby.so).
//   2. Tiap kali game membuka rekaman mic, pasang DSP BASS di channel itu.
//   3. DSP memproses audio mic dengan RubberBand LiveShifter (pitch + formant)
//      SEBELUM data sampai ke encoder voice SA-MP.
//   4. Kontrol dari Lua lewat struct `vc_api` (7 slot, URUTAN JANGAN DIUBAH).
//
//  Arti parameter:
//   pitch   = skala pitch.   1.0 normal, 2.0 = naik 1 oktaf, 0.5 = turun 1 oktaf
//   formant = skala formant. 1.0 normal (karakter/warna suara asli tetap)
//             >1 suara terdengar "lebih kecil/tipis", <1 "lebih besar/berat"
// =============================================================================
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>
#include <math.h>
#include <atomic>
#include <memory>
#include <mutex>
#include <vector>
#include <algorithm>
#include <string>
#include <thread>
#include <chrono>
#include <android/log.h>
#include <rubberband/RubberBandLiveShifter.h>

#define VFX_EXPORT extern "C" __attribute__((visibility("default")))
#define VFX_LOG_FILE "/storage/emulated/0/voicefx_log.txt"

// ----------------------------------------------------------------- logging --
static void vlog(const char* fmt, ...) {
    char buf[512];
    va_list ap; va_start(ap, fmt); vsnprintf(buf, sizeof buf, fmt, ap); va_end(ap);
    __android_log_print(ANDROID_LOG_INFO, "VoiceFX", "%s", buf);
    if (FILE* f = fopen(VFX_LOG_FILE, "a")) { fprintf(f, "[VFX] %s\n", buf); fclose(f); }
}

// ------------------------------------------------------------- BASS / Dobby --
typedef uint32_t DWORD;
typedef int      BOOL;
typedef BOOL (*RECORDPROC)(DWORD handle, const void* buffer, DWORD length, void* user);
typedef void (*DSPPROC)(DWORD handle, DWORD channel, void* buffer, DWORD length, void* user);
typedef DWORD (*BASS_RecordStart_t)(DWORD freq, DWORD chans, DWORD flags, RECORDPROC proc, void* user);
typedef DWORD (*BASS_ChannelSetDSP_t)(DWORD handle, DSPPROC proc, void* user, int priority);
typedef BOOL  (*BASS_ChannelRemoveDSP_t)(DWORD handle, DWORD dsp);
typedef int   (*DobbyHook_t)(void* address, void* replace, void** origin);
typedef void* (*DobbySymbolResolver_t)(const char* image, const char* symbol);

static BASS_RecordStart_t      g_origRecordStart = nullptr;
static BASS_ChannelSetDSP_t    g_setDSP          = nullptr;
static BASS_ChannelRemoveDSP_t g_removeDSP       = nullptr;

// -------------------------------------------------------------------- FIFO --
class Fifo {
public:
    void   clear()      { head_ = 0; n_ = 0; }
    size_t size() const { return n_; }
    void push(const float* p, size_t c) {
        reserve(n_ + c);
        const size_t cap = d_.size();
        const size_t tail = (head_ + n_) % cap;
        const size_t first = std::min(c, cap - tail);
        memcpy(&d_[tail], p, first * sizeof(float));
        if (c > first) memcpy(&d_[0], p + first, (c - first) * sizeof(float));
        n_ += c;
    }
    void pushZeros(size_t c) {
        reserve(n_ + c);
        const size_t cap = d_.size();
        for (size_t i = 0; i < c; i++) d_[(head_ + n_ + i) % cap] = 0.f;
        n_ += c;
    }
    void pop(float* out, size_t c) {
        const size_t cap = d_.size();
        for (size_t i = 0; i < c; i++) out[i] = (i < n_) ? d_[(head_ + i) % cap] : 0.f;
        const size_t k = std::min(c, n_);
        head_ = cap ? (head_ + k) % cap : 0;
        n_ -= k;
    }
private:
    void reserve(size_t need) {
        if (!d_.empty() && d_.size() >= need) return;
        std::vector<float> nd(std::max<size_t>(need * 2, 4096));
        for (size_t i = 0; i < n_; i++) nd[i] = d_[(head_ + i) % d_.size()];
        d_.swap(nd);
        head_ = 0;
    }
    std::vector<float> d_;
    size_t head_ = 0, n_ = 0;
};

// ------------------------------------------------------------------ Engine --
// Buffer BASS ukurannya bebas, RubberBand LiveShifter butuh blok tetap.
// Solusi: FIFO masuk -> proses per blok -> FIFO keluar. FIFO keluar diisi nol
// sebanyak 1 blok di awal, jadi jumlah sampel keluar selalu = jumlah masuk
// (latensi tambahan = 1 blok, sekitar 10 ms).
struct Engine {
    uint32_t rate = 0, ch = 0, flags = 0;
    size_t   block = 0;
    std::unique_ptr<RubberBand::RubberBandLiveShifter> rb;
    std::vector<Fifo> in, out;
    std::vector<std::vector<float>> bIn, bOut, tIn, tOut;
    std::vector<const float*> pIn;
    std::vector<float*>       pOut;
    double lastPitch = 1.0, lastFormant = 1.0;

    bool init(uint32_t sr, uint32_t chans, uint32_t fl) {
        if (chans < 1 || chans > 2 || sr < 4000 || (fl & 1u)) return false;  // 8-bit tidak didukung
        rate = sr; ch = chans; flags = fl;
        rb.reset(new RubberBand::RubberBandLiveShifter(
            sr, chans, RubberBand::RubberBandLiveShifter::OptionFormantPreserved));
        block = rb->getBlockSize();
        if (!block) return false;
        in.assign(ch, Fifo());
        out.assign(ch, Fifo());
        bIn.assign(ch, std::vector<float>(block));
        bOut.assign(ch, std::vector<float>(block));
        tIn.assign(ch, std::vector<float>());
        tOut.assign(ch, std::vector<float>());
        pIn.resize(ch); pOut.resize(ch);
        for (uint32_t c = 0; c < ch; c++) { pIn[c] = bIn[c].data(); pOut[c] = bOut[c].data(); }
        setParams(1.0, 1.0, true);
        restart();
        return true;
    }
    void setParams(double p, double f, bool force = false) {
        if (force || p != lastPitch)   { rb->setPitchScale(p);   lastPitch = p; }
        if (force || f != lastFormant) { rb->setFormantScale(f); lastFormant = f; }
    }
    void restart() {
        rb->reset();
        for (uint32_t c = 0; c < ch; c++) { in[c].clear(); out[c].clear(); out[c].pushZeros(block); }
    }
    void process(void* buf, uint32_t bytes, double p, double f) {
        const bool   flt = (flags & 256u) != 0;
        const size_t bps = flt ? 4 : 2;
        const size_t frames = bytes / (bps * ch);
        if (!frames) return;
        setParams(p, f);
        for (uint32_t c = 0; c < ch; c++) { tIn[c].resize(frames); tOut[c].resize(frames); }

        if (flt) {
            const float* s = (const float*)buf;
            for (size_t i = 0; i < frames; i++)
                for (uint32_t c = 0; c < ch; c++) tIn[c][i] = s[i * ch + c];
        } else {
            const int16_t* s = (const int16_t*)buf;
            for (size_t i = 0; i < frames; i++)
                for (uint32_t c = 0; c < ch; c++) tIn[c][i] = s[i * ch + c] * (1.0f / 32768.0f);
        }
        for (uint32_t c = 0; c < ch; c++) in[c].push(tIn[c].data(), frames);

        while (in[0].size() >= block) {
            for (uint32_t c = 0; c < ch; c++) in[c].pop(bIn[c].data(), block);
            rb->shift(pIn.data(), pOut.data());
            for (uint32_t c = 0; c < ch; c++) out[c].push(bOut[c].data(), block);
        }
        for (uint32_t c = 0; c < ch; c++) out[c].pop(tOut[c].data(), frames);

        if (flt) {
            float* d = (float*)buf;
            for (size_t i = 0; i < frames; i++)
                for (uint32_t c = 0; c < ch; c++) d[i * ch + c] = tOut[c][i];
        } else {
            int16_t* d = (int16_t*)buf;
            for (size_t i = 0; i < frames; i++)
                for (uint32_t c = 0; c < ch; c++) {
                    float v = tOut[c][i] * 32768.0f;   // skala sama dengan saat konversi masuk
                    v = v > 32767.f ? 32767.f : (v < -32768.f ? -32768.f : v);
                    d[i * ch + c] = (int16_t)lrintf(v);
                }
        }
    }
};

// ------------------------------------------------------------------ state ---
static std::atomic<bool>  g_enabled{false};
static std::atomic<float> g_pitch{1.0f};
static std::atomic<float> g_formant{1.0f};
static std::mutex         g_mtx;                 // melindungi 4 variabel di bawah
static std::unique_ptr<Engine> g_eng;
static bool  g_wasActive = false;
static DWORD g_chan = 0, g_dsp = 0;

// DSP dipanggil di thread audio BASS. JANGAN pernah memblokir thread ini:
// kalau mutex sedang dipegang, lewati (audio lewat tanpa efek untuk 1 buffer).
static void dspCallback(DWORD, DWORD, void* buffer, DWORD length, void*) {
    if (!g_enabled.load(std::memory_order_relaxed)) { 
        std::unique_lock<std::mutex> lk(g_mtx, std::try_to_lock);
        if (lk.owns_lock()) g_wasActive = false;
        return;
    }
    const float p = g_pitch.load(), f = g_formant.load();
    std::unique_lock<std::mutex> lk(g_mtx, std::try_to_lock);
    if (!lk.owns_lock() || !g_eng) return;
    if (fabsf(p - 1.f) < 0.005f && fabsf(f - 1.f) < 0.005f) { g_wasActive = false; return; }
    if (!g_wasActive) { g_eng->restart(); g_wasActive = true; }
    g_eng->process(buffer, length, p, f);
}

static void attachDSP(DWORD h, DWORD freq, DWORD chans, DWORD flags) {
    if (!g_setDSP) return;
    std::unique_ptr<Engine> e(new Engine());
    if (!e->init(freq, chans, flags)) {
        vlog("format rekaman tidak didukung: freq=%u chans=%u flags=0x%x", freq, chans, flags);
        return;
    }
    DWORD oldChan, oldDsp;
    {   // JANGAN panggil fungsi BASS sambil memegang mutex (risiko deadlock)
        std::lock_guard<std::mutex> lk(g_mtx);
        oldChan = g_chan; oldDsp = g_dsp;
        g_eng = std::move(e);
        g_chan = h; g_dsp = 0; g_wasActive = false;
    }
    if (oldChan && oldDsp && oldChan != h && g_removeDSP) g_removeDSP(oldChan, oldDsp);
    DWORD d = g_setDSP(h, dspCallback, nullptr, 0);
    { std::lock_guard<std::mutex> lk(g_mtx); g_dsp = d; }
    vlog("DSP terpasang: channel=%u freq=%u chans=%u flags=0x%x dsp=%u", h, freq, chans, flags, d);
}

static DWORD hook_BASSRecordStart(DWORD freq, DWORD chans, DWORD flags, RECORDPROC proc, void* user) {
    DWORD h = g_origRecordStart ? g_origRecordStart(freq, chans, flags, proc, user) : 0;
    if (h) attachDSP(h, freq, chans, flags);
    return h;
}

// ------------------------------------------------------------------ vc_api ---
static void  vc_set_pitch(float v)   { g_pitch.store(std::min(4.0f, std::max(0.25f, v))); }
static void  vc_enable()             { g_enabled.store(true);  }
static void  vc_disable()            { g_enabled.store(false); }
static bool  vc_is_enabled()         { return g_enabled.load(); }
static float vc_get_pitch()          { return g_pitch.load(); }
static void  vc_set_formant(float v) { g_formant.store(std::min(4.0f, std::max(0.25f, v))); }
static float vc_get_formant()        { return g_formant.load(); }

typedef struct {
    void  (*set_pitch)(float);
    void  (*enable)(void);
    void  (*disable)(void);
    bool  (*is_enabled)(void);
    float (*get_pitch)(void);
    void  (*set_formant)(float);
    float (*get_formant)(void);
} vc_api_t;

extern "C" {
__attribute__((visibility("default"))) vc_api_t vc_api = {
    vc_set_pitch, vc_enable, vc_disable, vc_is_enabled,
    vc_get_pitch, vc_set_formant, vc_get_formant
};
}

// ---------------------------------------------------------------- install ---
// Cari libdobby.so: (1) sudah dimuat? (2) nama biasa (3) satu folder dengan libvoicefx.so
static void* loadDobby() {
    void* h = dlopen("libdobby.so", RTLD_NOW | RTLD_NOLOAD);
    if (h) return h;
    h = dlopen("libdobby.so", RTLD_NOW);
    if (h) return h;
    Dl_info info;
    if (dladdr((void*)&loadDobby, &info) && info.dli_fname) {
        std::string path = info.dli_fname;
        size_t slash = path.rfind('/');
        if (slash != std::string::npos) {
            path = path.substr(0, slash + 1) + "libdobby.so";
            h = dlopen(path.c_str(), RTLD_NOW);
            vlog("coba libdobby di: %s -> %s", path.c_str(), h ? "OK" : "gagal");
            if (h) return h;
        }
    }
    const char* e = dlerror();
    vlog("ERROR: libdobby.so tidak ditemukan (%s)", e ? e : "-");
    return nullptr;
}

// return: 0 = sukses, 1 = coba lagi nanti (libBASS belum dimuat), -1 = gagal permanen
static int installHook() {
    // Sama seperti lib yang terbukti jalan: kalau libBASS belum dimuat game, muat sendiri
    // (soname sama, jadi game nanti memakai handle yang sama).
    void* hb = dlopen("libBASS.so", RTLD_NOW | RTLD_NOLOAD);
    if (!hb) hb = dlopen("libBASS.so", RTLD_NOW);
    if (!hb) return 1;

    g_setDSP    = (BASS_ChannelSetDSP_t)   dlsym(hb, "BASS_ChannelSetDSP");
    g_removeDSP = (BASS_ChannelRemoveDSP_t)dlsym(hb, "BASS_ChannelRemoveDSP");

    void* hd = loadDobby();
    if (!hd) return -1;
    DobbyHook_t dobbyHook = (DobbyHook_t)dlsym(hd, "DobbyHook");
    if (!dobbyHook) { vlog("ERROR: simbol DobbyHook tidak ada"); return -1; }
    void* target = nullptr;
    DobbySymbolResolver_t res = (DobbySymbolResolver_t)dlsym(hd, "DobbySymbolResolver");
    if (res) target = res("libBASS.so", "BASS_RecordStart");
    if (!target) target = dlsym(hb, "BASS_RecordStart");
    if (!target)    { vlog("ERROR: alamat BASS_RecordStart tidak ketemu"); return -1; }
    if (!g_setDSP)  { vlog("ERROR: BASS_ChannelSetDSP tidak ketemu");      return -1; }

    if (dobbyHook(target, (void*)hook_BASSRecordStart, (void**)&g_origRecordStart) != 0) {
        vlog("ERROR: DobbyHook gagal");
        return -1;
    }
    vlog("BASS_RecordStart di-hook (%p)", target);
    return 0;
}

VFX_EXPORT const char* __GetModInfo() { return "libvoicefx|3.0|VoiceFX RubberBand|VoiceChanger"; }

VFX_EXPORT void OnModPreLoad() {
    remove(VFX_LOG_FILE);
    vlog("OnModPreLoad");
}

VFX_EXPORT void OnModLoad() {
    vlog("OnModLoad");
    { Dl_info self; if (dladdr((void*)&OnModLoad, &self) && self.dli_fname) vlog("libvoicefx dimuat dari: %s", self.dli_fname); }
    int r = installHook();
    if (r == 1) {
        // libBASS.so belum bisa dimuat -> coba lagi tiap 1 detik, maks 30 menit
        std::thread([] {
            for (int i = 0; i < 1800; i++) {
                std::this_thread::sleep_for(std::chrono::milliseconds(1000));
                int rr = installHook();
                if (rr <= 0) { if (rr == 0) vlog("hook terpasang setelah menunggu"); return; }
            }
            vlog("ERROR: libBASS.so tidak bisa dimuat (menyerah)");
        }).detach();
    }
    vlog("OnModLoad selesai (status=%d)", r);
}
