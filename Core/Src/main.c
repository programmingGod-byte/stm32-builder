/* USER CODE BEGIN Header */
/**
  ******************************************************************************
  * @file           : main.c
  * @brief          : Main program body
  ******************************************************************************
  * @attention
  *
  * Copyright (c) 2025 STMicroelectronics.
  * All rights reserved.
  *
  * This software is licensed under terms that can be found in the LICENSE file
  * in the root directory of this software component.
  * If no LICENSE file comes with this software, it is provided AS-IS.
  *
  ******************************************************************************
  */
/* USER CODE END Header */
/* Includes ------------------------------------------------------------------*/
#include "main.h"

/* Private includes ----------------------------------------------------------*/
/* USER CODE BEGIN Includes */
#include <string.h>
#include <stdio.h>
#include <stdbool.h>
#include <math.h>
#include "arm_math.h"
#include "arm_const_structs.h"

/* USER CODE END Includes */

/* Private typedef -----------------------------------------------------------*/
/* USER CODE BEGIN PTD */

/* USER CODE END PTD */

/* Private define ------------------------------------------------------------*/
/* USER CODE BEGIN PD */

/* USER CODE END PD */

/* Private macro -------------------------------------------------------------*/
/* USER CODE BEGIN PM */

/* USER CODE END PM */

/* Private variables ---------------------------------------------------------*/
ADC_HandleTypeDef hadc1;
DMA_HandleTypeDef hdma_adc1;

TIM_HandleTypeDef htim2;

UART_HandleTypeDef huart2;
UART_HandleTypeDef huart3;
UART_HandleTypeDef huart6;
DMA_HandleTypeDef hdma_usart3_tx;

PCD_HandleTypeDef hpcd_USB_OTG_FS;

/* USER CODE BEGIN PV */
volatile uint8_t uart3_tx_done = 1;

#define KMC_PERIOD_MS        1000U     // 1 Hz KMC slots
#define VLD_SPREAD_MS        4000U     // every 4 seconds => ~15 reads/min
#define VLD_MAX_PER_MIN      20U
#define VLD_MIN_PER_MIN      10U       // (not enforced; just target)


#define KMC_PEAK_REL_GATE  0.20f   // gate at 20% of peak power (tune if needed)
#define KMC_FD_MIN_HZ      0.5f    // Doppler band min (example)
#define KMC_FD_MAX_HZ      200.0f  // Doppler band max (example)

#define FS_HZ_INT           3200U
#define CAPTURE_SEC         1U
#define CH_COUNT            2U

#define IQ_PAIRS_PER_CAP    (FS_HZ_INT * CAPTURE_SEC)   // 2400
#define DMA_LEN             (IQ_PAIRS_PER_CAP * CH_COUNT) // 4800 uint16


#define FS_HZ               3200.0f
#define WINDOW_SEC          5
#define IQ_PAIRS_PER_HALF   ((uint32_t)(FS_HZ * WINDOW_SEC))
//#define CH_COUNT            2
//#define DMA_LEN             (IQ_PAIRS_PER_HALF * CH_COUNT * 2)
#define REPORT_EVERY_SEC    5
#define FTX_HZ              24.125e9f
#define C_MPS               3.0e8f

/* Defines from vld1.c (V-LD1 Radar) */
#define N_READS             15
//#define CAPTURE_PERIOD_MS   (1 * 60 * 1000)
#define SIGNAL_TIMEOUT_MS   (2 * 60 * 1000)
#define RELAY_COOLDOWN_MS   (1 * 60 * 1000)

/* Hardware Pin Mapping */
#define RELAY_PIN           GPIO_PIN_10
#define RELAY_PORT          GPIOA
#define TRIGGER_PIN         GPIO_PIN_3
#define TRIGGER_PORT        GPIOB

/* ===== Python-equivalent KMC1 processing settings ===== */
#define FS_HZ_F                 3200.0f
#define RADAR_F0_HZ             24.125e9f
#define CORRECTION_ANGLE_DEG    65.0f

#define BATCH_DURATION_SEC      1U
#define AGG_WINDOW_SEC          60U
#define SLEEP_WINDOW_SEC        240U

#define SAMPLES_PER_BATCH       ((uint32_t)(FS_HZ_F * (float)BATCH_DURATION_SEC)) // 3200
#define KMC_NFFT                4096U   // matches Python outcome

#define MIN_SNR_DB              3.0f
#define THRESH_FRAC_OF_SNR      0.50f
#define CLUTTER_THRESH_MPS      0.15f

// Direction: Python uses 'RECEDING' to take negative-frequency half
#define RIVER_RECEDING          1

static float kmc_fft_buf[2 * KMC_NFFT];          // complex buffer (Re,Im,...)
static float kmc_win[SAMPLES_PER_BATCH];         // Hann window length 3200

static float BIN_TO_VEL;                          // m/s per FFT bin (radial)
static float COS_CORR;                            // cos(angle)


/* ===== IQ streaming over UART3 (binary framed) ===== */
#define IQ_MAGIC0 'I'
#define IQ_MAGIC1 'Q'
#define IQ_MAGIC2 'P'
#define IQ_MAGIC3 'K'
#define IQ_HDR_LEN 20

static volatile uint8_t  iq_tx_busy  = 0;
static volatile uint8_t  iq_tx_stage = 0;   // 0=idle, 1=hdr, 2=payload
static uint8_t           iq_hdr[IQ_HDR_LEN];
static uint32_t          iq_seq = 0;

static uint8_t          *iq_payload_ptr = NULL;
static uint32_t          iq_payload_len = 0;

/* --- Median filter state (keep even if unused) --- */
#define MED_WIN 12
static float   fd_win[MED_WIN];
static uint8_t fd_win_idx   = 0;
static uint8_t fd_win_count = 0;
/* USER CODE END PV */

/* Private function prototypes -----------------------------------------------*/
void SystemClock_Config(void);
static void MPU_Config(void);
static void MX_GPIO_Init(void);
static void MX_DMA_Init(void);
static void MX_USART3_UART_Init(void);
static void MX_USB_OTG_FS_PCD_Init(void);
static void MX_USART6_UART_Init(void);
static void MX_TIM2_Init(void);
static void MX_USART2_UART_Init(void);
static void MX_ADC1_Init(void);
/* USER CODE BEGIN PFP */

/* USER CODE END PFP */

/* Private user code ---------------------------------------------------------*/
/* USER CODE BEGIN 0 */
/* Global Variables */

#define KMC_READS_PER_CYCLE   60
#define VLD_READS_PER_CYCLE   10

typedef enum { STATE_KMC = 0, STATE_VLD1 = 1 } capture_state_t;
static capture_state_t cap_state = STATE_KMC;

static uint32_t kmc_count = 0;
static uint32_t vld_count = 0;
//static float vld_vals[VLD_MAX_PER_MIN];
//uint32_t vld_n = 0;
//uint32_t next_vld_ms = HAL_GetTick();  // schedule first attempt immediately (or +1000)


extern UART_HandleTypeDef huart2;
extern UART_HandleTypeDef huart3;
extern UART_HandleTypeDef huart6;
extern ADC_HandleTypeDef hadc1;
extern TIM_HandleTypeDef htim2;

/* KMC1 State Variables */
uint16_t adc_dma[DMA_LEN];
volatile uint8_t half_ready = 0;
volatile uint8_t full_ready = 0;
static float v_hist[REPORT_EVERY_SEC];
static uint8_t v_hist_idx = 0;
static uint8_t v_hist_count = 0;
//static float fd_filt = 0.0f;
//static const float beta = 0.8f;
static float cos_tilt = 1.0f;

/* V-LD1 State Variables */
//uint32_t nextCaptureAt = 0;
uint32_t lastSignalTime = 0;
uint32_t cooldownStart = 0;
bool cooldownActive = false;

uint8_t INIT_CMD[] = { 'I','N','I','T', 0x01, 0x00, 0x00, 0x00, 0x00 };
uint8_t GNFD_CMD[] = { 'G','N','F','D', 0x01, 0x00, 0x00, 0x00, 0x04 };
uint8_t START_CMD[] = { 'S','T','R','T', 0x01, 0x00, 0x00, 0x00, 0x01 };

int _write(int file, char *ptr, int len) {
    HAL_UART_Transmit(&huart2, (uint8_t*)ptr, len, HAL_MAX_DELAY);
    return len;
}

/* KMC1 Helper Functions (from main.c) */
static float estimate_fd_hz(const uint16_t *iq, int pairs, float fs_hz) {
    float meanI = 0, meanQ = 0;
    for (int n=0; n<pairs; n++) { meanI += iq[2*n+0]; meanQ += iq[2*n+1]; }
    meanI /= pairs; meanQ /= pairs;

    float prev = 0, sum_dphi = 0;
    for (int n=0; n<pairs; n++) {
        float I = (float)iq[2*n+0] - meanI;
        float Q = (float)iq[2*n+1] - meanQ;
        float phi = atan2f(Q, I);
        if (n>0) {
            float d = phi - prev;
            if (d > (float)M_PI) d -= (float)(2.0*M_PI);
            if (d < -(float)M_PI) d += (float)(2.0*M_PI);
            sum_dphi += d;
        }
        prev = phi;
    }
    return (fs_hz / (2.0f*(float)M_PI)) * (sum_dphi / (pairs-1));
}

static float fd_to_velocity_mps(float fd_hz) {
    return (C_MPS / (2.0f * FTX_HZ)) * fd_hz;
}

/* V-LD1 Helper Functions (from vld1.c) */
HAL_StatusTypeDef readPacket(char* hdr, uint8_t* payload, uint32_t* outLen) {
    uint8_t lenb[4];
    __HAL_UART_CLEAR_IT(&huart6, UART_CLEAR_OREF | UART_CLEAR_NEF | UART_CLEAR_FEF | UART_CLEAR_PEF);
    if (HAL_UART_Receive(&huart6, (uint8_t*)hdr, 4, 300) != HAL_OK) return HAL_TIMEOUT;
    if (HAL_UART_Receive(&huart6, lenb, 4, 100) != HAL_OK) return HAL_TIMEOUT;
    uint32_t len = (uint32_t)lenb[0] | (lenb[1] << 8) | (lenb[2] << 16) | (lenb[3] << 24);
    *outLen = len;
    if (len > 256 || len == 0) return HAL_ERROR;
    return HAL_UART_Receive(&huart6, payload, len, 300);
}

void relayFSM() {
    uint32_t now = HAL_GetTick();
    bool trigger = HAL_GPIO_ReadPin(TRIGGER_PORT, TRIGGER_PIN) == GPIO_PIN_SET;
    if (trigger) {
        lastSignalTime = now;
        if (!cooldownActive) {
            HAL_GPIO_WritePin(RELAY_PORT, RELAY_PIN, GPIO_PIN_SET);
            cooldownActive = true; cooldownStart = now;
        }
    }
    if (!cooldownActive && (now - lastSignalTime >= SIGNAL_TIMEOUT_MS)) {
        HAL_GPIO_WritePin(RELAY_PORT, RELAY_PIN, GPIO_PIN_SET);
        cooldownActive = true; cooldownStart = now;
    }
    if (cooldownActive && (now - cooldownStart >= RELAY_COOLDOWN_MS)) {
        HAL_GPIO_WritePin(RELAY_PORT, RELAY_PIN, GPIO_PIN_RESET);
        cooldownActive = false; lastSignalTime = now;
    }
}

float medianOf(float *arr, int n) {
    float tmp[N_READS];
    for (int i = 0; i < n; ++i) tmp[i] = arr[i];
    for (int i = 1; i < n; ++i) {
        float key = tmp[i]; int j = i - 1;
        while (j >= 0 && tmp[j] > key) { tmp[j + 1] = tmp[j]; --j; }
        tmp[j + 1] = key;
    }
    return (n % 2 != 0) ? tmp[n / 2] : 0.5f * (tmp[n / 2 - 1] + tmp[n / 2]);
}

/* ===== KMC1 FFT helpers ===== */

static void kmc1_init_hann_window(void)
{
    // Hann window length = SAMPLES_PER_BATCH (3200)
    // w[n] = 0.5*(1 - cos(2*pi*n/(N-1)))
    for (uint32_t n = 0; n < SAMPLES_PER_BATCH; n++)
    {
        kmc_win[n] = 0.5f * (1.0f - cosf((2.0f * (float)M_PI * (float)n) / (float)(SAMPLES_PER_BATCH - 1)));
    }

    COS_CORR = cosf(CORRECTION_ANGLE_DEG * (float)M_PI / 180.0f);

    // bin_to_vel_factor = (Fs/NFFT) * (lambda/2)
    // lambda = c/f0
    BIN_TO_VEL = (FS_HZ_F / (float)KMC_NFFT) * ((3.0e8f / RADAR_F0_HZ) * 0.5f);
}

static float kmc_process_one_batch_python(const uint16_t *iq_u16,
                                          float *out_snr_db,
                                          float *out_width_mps)
{
    // ---- 0) DC remove (detrend) on 3200 samples ----
    float meanI = 0.0f, meanQ = 0.0f;
    for (uint32_t n = 0; n < SAMPLES_PER_BATCH; n++)
    {
        meanI += (float)iq_u16[2*n + 0];
        meanQ += (float)iq_u16[2*n + 1];
    }
    meanI /= (float)SAMPLES_PER_BATCH;
    meanQ /= (float)SAMPLES_PER_BATCH;

    // ---- 1) Window + pack into FFT buffer (zero-pad to 4096) ----
    for (uint32_t n = 0; n < SAMPLES_PER_BATCH; n++)
    {
        float I = ((float)iq_u16[2*n + 0] - meanI) * kmc_win[n];
        float Q = ((float)iq_u16[2*n + 1] - meanQ) * kmc_win[n];
        kmc_fft_buf[2*n + 0] = I;
        kmc_fft_buf[2*n + 1] = Q;
    }
    for (uint32_t n = SAMPLES_PER_BATCH; n < KMC_NFFT; n++)
    {
        kmc_fft_buf[2*n + 0] = 0.0f;
        kmc_fft_buf[2*n + 1] = 0.0f;
    }

    // ---- 2) FFT (complex) ----
    arm_cfft_f32(&arm_cfft_sR_f32_len4096, kmc_fft_buf, 0, 1);

    // ---- 3) Power spectrum stats: mean power + peak power ----
    // Python: mag_sq = abs(spectrum)^2
    // noise_floor_db = 10log10(mean(mag_sq)+1e-9)
    // peak_db = max(10log10(mag_sq+1e-9))
    const float eps = 1e-9f;

    float sumP = 0.0f;
    float pmax = 0.0f;

    for (uint32_t k = 0; k < KMC_NFFT; k++)
    {
        float re = kmc_fft_buf[2*k + 0];
        float im = kmc_fft_buf[2*k + 1];
        float p  = re*re + im*im;
        sumP += p;
        if (p > pmax) pmax = p;
    }

    float meanP = sumP / (float)KMC_NFFT;
    float noise_db = 10.0f * log10f(meanP + eps);
    float peak_db  = 10.0f * log10f(pmax  + eps);
    float snr_db   = peak_db - noise_db;

    if (out_snr_db) *out_snr_db = snr_db;

    // ---- 4) SNR gate ----
    if (snr_db < MIN_SNR_DB || !isfinite(snr_db))
    {
        if (out_width_mps) *out_width_mps = 0.0f;
        return 0.0f;
    }

    // ---- 5) Threshold: noise + 0.20 * dynamic_range (which = snr) ----
    float thresh_db  = noise_db + (THRESH_FRAC_OF_SNR * snr_db);
    float thresh_lin = powf(10.0f, thresh_db / 10.0f);

    // ---- 6) Centroid over selected bins (Python direction logic) ----
    // Python:
    // if RECEDING: bins i = N/2..N-1, idx_shifted = i - N (negative)
    // vel = idx_shifted * BIN_TO_VEL
    // skip abs(vel) < clutter
    // if spectrum_db[i] > threshold_db => include (equivalent to p > thresh_lin)
    float num = 0.0f, den = 0.0f;

#if RIVER_RECEDING
    uint32_t start_bin = KMC_NFFT / 2;
    uint32_t end_bin   = KMC_NFFT;
#else
    uint32_t start_bin = 1;
    uint32_t end_bin   = KMC_NFFT / 2;
#endif

    for (uint32_t i = start_bin; i < end_bin; i++)
    {
#if RIVER_RECEDING
        int32_t idx_shifted = (int32_t)i - (int32_t)KMC_NFFT;
#else
        int32_t idx_shifted = (int32_t)i;
#endif
        float vel = (float)idx_shifted * BIN_TO_VEL;

        if (fabsf(vel) < CLUTTER_THRESH_MPS) continue;

        float re = kmc_fft_buf[2*i + 0];
        float im = kmc_fft_buf[2*i + 1];
        float p  = re*re + im*im;

        if (p > thresh_lin)
        {
            num += vel * p;
            den += p;
        }
    }

    if (den <= 0.0f || !isfinite(den))
    {
        if (out_width_mps) *out_width_mps = 0.0f;
        return 0.0f;
    }

    float centroid_radial = num / den;         // m/s (radial)
    float centroid_corr   = centroid_radial / COS_CORR;

    // ---- 7) Spectral width (weighted stddev around centroid_radial) ----
    float var_num = 0.0f;

    for (uint32_t i = start_bin; i < end_bin; i++)
    {
#if RIVER_RECEDING
        int32_t idx_shifted = (int32_t)i - (int32_t)KMC_NFFT;
#else
        int32_t idx_shifted = (int32_t)i;
#endif
        float vel = (float)idx_shifted * BIN_TO_VEL;

        if (fabsf(vel) < CLUTTER_THRESH_MPS) continue;

        float re = kmc_fft_buf[2*i + 0];
        float im = kmc_fft_buf[2*i + 1];
        float p  = re*re + im*im;

        if (p > thresh_lin)
        {
            float d = (vel - centroid_radial);
            var_num += p * (d * d);
        }
    }

    float variance = var_num / den;
    float width = (variance > 0.0f) ? sqrtf(variance) : 0.0f; // radial width

    if (out_width_mps) *out_width_mps = width / COS_CORR;

    // Python returns abs(centroid_corrected)
    float v_out = fabsf(centroid_corr);
    if (!isfinite(v_out)) v_out = 0.0f;
    return v_out;
}



static float kmc1_centroid_from_fft_side(const float *X, float fs_hz,
                                         int use_negative_side,
                                         int kmin, int kmax)
{
    // X is interleaved complex FFT output length NFFT (Re,Im,...)
    // If use_negative_side=0: use bins k=1..N/2-1 (positive)
    // If use_negative_side=1: use bins k=N-1..N/2+1 (negative mapped to +freq magnitude)

    float pmax = 0.0f;

    // 1) find peak power in band (for gating)
    if (!use_negative_side)
    {
        for (int k = kmin; k <= kmax; k++)
        {
            float re = X[2*k + 0];
            float im = X[2*k + 1];
            float p  = re*re + im*im;
            if (p > pmax) pmax = p;
        }
    }
    else
    {
        // negative side bin index maps: freq_mag = fs*(N-k)/N
        for (int kmag = kmin; kmag <= kmax; kmag++)
        {
            int k = KMC_NFFT - kmag; // bin corresponding to -freq_mag
            float re = X[2*k + 0];
            float im = X[2*k + 1];
            float p  = re*re + im*im;
            if (p > pmax) pmax = p;
        }
    }

    if (pmax <= 0.0f) return 0.0f;

    float gate = pmax * KMC_PEAK_REL_GATE;

    // 2) centroid
    float sumP = 0.0f;
    float sumFP = 0.0f;

    if (!use_negative_side)
    {
        for (int k = kmin; k <= kmax; k++)
        {
            float re = X[2*k + 0];
            float im = X[2*k + 1];
            float p  = re*re + im*im;
            if (p < gate) continue;

            float f = (fs_hz * (float)k) / (float)KMC_NFFT;
            sumP  += p;
            sumFP += f * p;
        }
    }
    else
    {
        for (int kmag = kmin; kmag <= kmax; kmag++)
        {
            int k = KMC_NFFT - kmag;
            float re = X[2*k + 0];
            float im = X[2*k + 1];
            float p  = re*re + im*im;
            if (p < gate) continue;

            float fmag = (fs_hz * (float)kmag) / (float)KMC_NFFT; // magnitude
            sumP  += p;
            sumFP += fmag * p;
        }
    }

    if (sumP <= 0.0f) return 0.0f;
    return sumFP / sumP; // fd magnitude in Hz
}

static float estimate_fd_fft_hz(const uint16_t *iq, int pairs, float fs_hz,
                                float *out_meanI, float *out_meanQ)
{
    // We use first KMC_NFFT complex samples (I,Q) from iq[2*n], iq[2*n+1]
    // pairs must be >= KMC_NFFT
    if (pairs < KMC_NFFT) return 0.0f;

    // 1) mean removal (DC)
    float meanI = 0.0f, meanQ = 0.0f;
    for (int n = 0; n < KMC_NFFT; n++)
    {
        meanI += (float)iq[2*n + 0];
        meanQ += (float)iq[2*n + 1];
    }
    meanI /= (float)KMC_NFFT;
    meanQ /= (float)KMC_NFFT;
    if (out_meanI) *out_meanI = meanI;
    if (out_meanQ) *out_meanQ = meanQ;

    // 2) window + pack complex buffer for FFT
    for (int n = 0; n < KMC_NFFT; n++)
    {
        float I = ((float)iq[2*n + 0] - meanI) * kmc_win[n];
        float Q = ((float)iq[2*n + 1] - meanQ) * kmc_win[n];

        kmc_fft_buf[2*n + 0] = I;
        kmc_fft_buf[2*n + 1] = Q;
    }

    // 3) complex FFT (in-place)
    arm_cfft_f32(&arm_cfft_sR_f32_len4096, kmc_fft_buf, 0, 1);

    // 4) choose Doppler band bins
    int kmin = (int)ceilf((KMC_FD_MIN_HZ * (float)KMC_NFFT) / fs_hz);
    int kmax = (int)floorf((KMC_FD_MAX_HZ * (float)KMC_NFFT) / fs_hz);

    if (kmin < 1) kmin = 1;
    if (kmax > (KMC_NFFT/2 - 1)) kmax = (KMC_NFFT/2 - 1);
    if (kmax <= kmin) return 0.0f;

    // 5) compute centroid on both sides, pick the side with higher total gated energy
    // (river direction may map to + or - Doppler depending on mounting)
    float fd_pos = kmc1_centroid_from_fft_side(kmc_fft_buf, fs_hz, 0, kmin, kmax);
    float fd_neg = kmc1_centroid_from_fft_side(kmc_fft_buf, fs_hz, 1, kmin, kmax);

    // pick the larger centroid result only if the other is ~0; otherwise pick the side with bigger fd (practical)
    // (simple heuristic; robust enough for river surface speed magnitude)
    float fd = (fd_pos >= fd_neg) ? fd_pos : fd_neg;
    return fd; // magnitude in Hz
}

static float running_median_fd_push(float x)
{
    // push into ring buffer
    fd_win[fd_win_idx] = x;
    fd_win_idx = (fd_win_idx + 1) % MED_WIN;
    if (fd_win_count < MED_WIN) fd_win_count++;

    // copy current window to temp
    float tmp[MED_WIN];
    for (uint8_t i = 0; i < fd_win_count; i++) tmp[i] = fd_win[i];

    // insertion sort (MED_WIN is tiny)
    for (uint8_t i = 1; i < fd_win_count; i++) {
        float key = tmp[i];
        int j = (int)i - 1;
        while (j >= 0 && tmp[j] > key) {
            tmp[j + 1] = tmp[j];
            j--;
        }
        tmp[j + 1] = key;
    }

    // median
    if (fd_win_count & 1) {
        return tmp[fd_win_count / 2];
    } else {
        uint8_t m = fd_win_count / 2;
        return 0.5f * (tmp[m - 1] + tmp[m]);
    }
}

static void uart3_send_blocking(const uint8_t *buf, uint32_t len)
{
    while (len)
    {
        uint16_t n = (len > 1024) ? 1024 : (uint16_t)len;
        HAL_UART_Transmit(&huart3, (uint8_t*)buf, n, HAL_MAX_DELAY);
        buf += n;
        len -= n;
    }
}

static int vld1_read_distance_once(float *out_m)
{
    // Returns:
    //  0  -> got PDAT float distance
    // -1  -> no valid PDAT this attempt (timeout/other packet)
    // -2  -> UART error

    // Clear UART6 errors + flush RX (same as your standalone code)
    __HAL_UART_CLEAR_IT(&huart6, UART_CLEAR_OREF | UART_CLEAR_NEF | UART_CLEAR_FEF | UART_CLEAR_PEF);
    __HAL_UART_SEND_REQ(&huart6, UART_RXDATA_FLUSH_REQUEST);

    // Trigger acquisition (ACQI)
    uint8_t ACQI_CMD[] = { 'A','C','Q','I', 0x01, 0x00, 0x00, 0x00, 0x00 };
    if (HAL_UART_Transmit(&huart6, ACQI_CMD, sizeof(ACQI_CMD), 50) != HAL_OK) return -2;

    // Drain one packet quickly if any (ACQI response etc). Don’t care if it fails.
    {
        char dh[4]; uint8_t dp[256]; uint32_t dl;
        (void)readPacket(dh, dp, &dl);
    }

    HAL_Delay(100);

    // Request PDAT only
    if (HAL_UART_Transmit(&huart6, GNFD_CMD, sizeof(GNFD_CMD), 50) != HAL_OK) return -2;

    char hdr[5] = {0};
    uint8_t payload[256];
    uint32_t pLen = 0;

    // First read
    if (readPacket(hdr, payload, &pLen) != HAL_OK) return -1;

    if (strncmp(hdr, "PDAT", 4) == 0)
    {
        if (pLen < 4) return -1;
        memcpy(out_m, payload, 4);
        return 0;
    }

    // If it was RESP, your sensor sometimes sends PDAT right after
    if (strncmp(hdr, "RESP", 4) == 0)
    {
        if (readPacket(hdr, payload, &pLen) != HAL_OK) return -1;
        if (strncmp(hdr, "PDAT", 4) == 0)
        {
            if (pLen < 4) return -1;
            memcpy(out_m, payload, 4);
            return 0;
        }
    }

    return -1;
}

static int vld1_read_distance_once_fast(float *out_m)
{
    // Clear errors + flush RX (critical)
    __HAL_UART_CLEAR_IT(&huart6, UART_CLEAR_OREF | UART_CLEAR_NEF | UART_CLEAR_FEF | UART_CLEAR_PEF);
    __HAL_UART_SEND_REQ(&huart6, UART_RXDATA_FLUSH_REQUEST);

    // 1) ACQI
    uint8_t ACQI_CMD[] = { 'A','C','Q','I', 0x01, 0x00, 0x00, 0x00, 0x00 };
    if (HAL_UART_Transmit(&huart6, ACQI_CMD, sizeof(ACQI_CMD), 50) != HAL_OK) return -2;

    // 2) IMPORTANT: read & discard ONE packet (usually ACQI RESP)
    {
        char dh[4]; uint8_t dp[256]; uint32_t dl = 0;
        (void)readPacket(dh, dp, &dl);
    }

    // Give sensor time to prepare PDAT (your working code uses ~100ms)
    HAL_Delay(100);

    // 3) GNFD (request distance)
    if (HAL_UART_Transmit(&huart6, GNFD_CMD, sizeof(GNFD_CMD), 50) != HAL_OK) return -2;

    // 4) Read up to a few packets until PDAT arrives
    for (int tries = 0; tries < 3; tries++)
    {
        char hdr[5] = {0};
        uint8_t payload[256];
        uint32_t pLen = 0;

        if (readPacket(hdr, payload, &pLen) != HAL_OK) return -1;

        if (strncmp(hdr, "PDAT", 4) == 0)
        {
            if (pLen < 4) return -1;
            memcpy(out_m, payload, 4);
            return 0;
        }

        // Sometimes: RESP then PDAT (so loop again)
        if (strncmp(hdr, "RESP", 4) == 0)
        {
            continue;
        }

        // Anything else: keep looping a couple times
    }

    return -1;
}



static void uart3_send_vld1_pkt(uint32_t cycle_seq, uint32_t idx, float dist_m, uint8_t ok)
{
    // JSON: {"T":"VLD","S":%lu,"i":%lu,"d":%.3f,"ok":%d}
    char json_buf[128];
    int json_len = snprintf(json_buf, sizeof(json_buf),
        "{\"T\":\"VLD\",\"S\":%lu,\"i\":%lu,\"d\":%.3f,\"ok\":%d}\n",
        (unsigned long)cycle_seq, (unsigned long)idx, dist_m, ok);

    if (json_len > 0)
    {
        HAL_UART_Transmit(&huart3, (uint8_t*)json_buf, (uint16_t)json_len, HAL_MAX_DELAY);
    }
}

static void sleep_ms_with_relay(uint32_t ms)
{
    uint32_t t0 = HAL_GetTick();
    while ((uint32_t)(HAL_GetTick() - t0) < ms)
    {
        relayFSM();          // keep relay logic alive
        HAL_Delay(25);       // small chunk
    }
}

static void vld1_drain_packets(uint32_t max_ms)
{
    uint32_t t0 = HAL_GetTick();
    while ((uint32_t)(HAL_GetTick() - t0) < max_ms)
    {
        char hdr[4];
        uint8_t pl[256];
        uint32_t len = 0;

        // Try to read a packet quickly; if none, stop draining.
        if (readPacket(hdr, pl, &len) != HAL_OK) break;
    }
}


/* USER CODE END 0 */

/**
  * @brief  The application entry point.
  * @retval int
  */
int main(void)
{

  /* USER CODE BEGIN 1 */

  /* USER CODE END 1 */

  /* MPU Configuration--------------------------------------------------------*/
  MPU_Config();

  /* MCU Configuration--------------------------------------------------------*/

  /* Reset of all peripherals, Initializes the Flash interface and the Systick. */
  HAL_Init();

  /* USER CODE BEGIN Init */

  /* USER CODE END Init */

  /* Configure the system clock */
  SystemClock_Config();

  /* USER CODE BEGIN SysInit */

  /* USER CODE END SysInit */

  /* Initialize all configured peripherals */
  MX_GPIO_Init();
  MX_DMA_Init();
  MX_USART3_UART_Init();
  MX_USB_OTG_FS_PCD_Init();
  MX_USART6_UART_Init();
  MX_TIM2_Init();
  MX_USART2_UART_Init();
  MX_ADC1_Init();
  /* USER CODE BEGIN 2 */
  // Give system time to stabilize after power-on (Relay switch-on can be noisy or slow)
  HAL_Delay(3000);

  printf("KMC1 + V-LD1 System Started\r\n");
  kmc1_init_hann_window();

  /* Initialise V-LD1 Radar */
  // ---- VLD1 Sensor init ----
  __HAL_UART_CLEAR_IT(&huart6, UART_CLEAR_OREF | UART_CLEAR_NEF | UART_CLEAR_FEF | UART_CLEAR_PEF);
  __HAL_UART_SEND_REQ(&huart6, UART_RXDATA_FLUSH_REQUEST);

  HAL_UART_Transmit(&huart6, INIT_CMD, sizeof(INIT_CMD), 100);
  HAL_Delay(120);

  HAL_UART_Transmit(&huart6, START_CMD, sizeof(START_CMD), 100);
  HAL_Delay(120);

  // Consume any START/RESP packets so the stream is aligned before first ACQI/GNFD
  vld1_drain_packets(300);

  cos_tilt = cosf(65.0f * (float)M_PI / 180.0f);

  /* Relay initial state */
  lastSignalTime = HAL_GetTick();
  HAL_GPIO_WritePin(RELAY_PORT, RELAY_PIN, GPIO_PIN_RESET);

  printf("--- Phase 1: VLD1 Capture (10 samples) ---\r\n");

  int vld_ok_count = 0;
  int vld_attempts = 0;

  while (vld_ok_count < 10 && vld_attempts < 80)
  {
      vld_attempts++;
      relayFSM();

      float dist_m = 0.0f;
      int res = vld1_read_distance_once_fast(&dist_m);

      if (res == 0 && isfinite(dist_m))
      {
          vld_ok_count++;

          // Print (goes to _write UART)
          printf("VLD Sample %d: %.3f m\r\n", vld_ok_count, dist_m);

          // Send to UART3 JSON (goes to Quectel / logger)
          uart3_send_vld1_pkt(0, vld_ok_count, dist_m, 1);

          // small spacing between successful reads
          HAL_Delay(120);
      }
      else
      {
          // Small backoff so we don’t spam sensor and desync again
          HAL_Delay(80);
      }
  }

  if (vld_ok_count < 10)
  {
      printf("Warning: VLD1 capture incomplete (%d/10), attempts=%d\r\n", vld_ok_count, vld_attempts);
  }
  else
  {
      printf("VLD1 Capture Complete.\r\n");
  }

  /* USER CODE END 2 */


  /* Infinite loop */
  /* USER CODE BEGIN WHILE */
  while (1)
  {
      static uint32_t seq = 0;

      float vel_list[AGG_WINDOW_SEC];
      float snr_sum = 0.0f;
      float wid_sum = 0.0f;
      uint32_t valid = 0;

      // =========================================================
      //  PHASE 2: KMC1 Infinite Loop
      // =========================================================
      for (uint32_t s = 0; s < AGG_WINDOW_SEC; s++)
      {
          uint32_t t0 = HAL_GetTick();
          uint32_t slot_deadline = t0 + KMC_PERIOD_MS;

          relayFSM();

          // ---- CAPTURE 1 second ----
          full_ready = 0;

          HAL_GPIO_WritePin(GPIOB, LD2_Pin, GPIO_PIN_SET);
          HAL_GPIO_WritePin(GPIOB, LD3_Pin, GPIO_PIN_RESET);

          HAL_TIM_Base_Start(&htim2);
          HAL_ADC_Start_DMA(&hadc1, (uint32_t*)adc_dma, DMA_LEN);
          while (!full_ready) { }

          HAL_ADC_Stop_DMA(&hadc1);
          HAL_TIM_Base_Stop(&htim2);

          HAL_GPIO_WritePin(GPIOB, LD2_Pin, GPIO_PIN_RESET);

          // ---- PROCESS ----
          float snr_db = 0.0f, width_mps = 0.0f;
          float vel_mps = kmc_process_one_batch_python(adc_dma, &snr_db, &width_mps);

          if (vel_mps > 0.0f && isfinite(vel_mps))
          {
              vel_list[valid++] = vel_mps;
              snr_sum += snr_db;
              wid_sum += width_mps;
          }

          // ---- SEND KMC frame (JSON) ----
          seq++;
          uint32_t t_ms = HAL_GetTick();

          char json_buf[128];
          int json_len = snprintf(json_buf, sizeof(json_buf),
              "{\"T\":\"KMC\",\"S\":%lu,\"tm\":%lu,\"v\":%.4f,\"s\":%.2f,\"w\":%.4f}\n",
              (unsigned long)seq, (unsigned long)t_ms, vel_mps, snr_db, width_mps);

          if (json_len > 0)
          {
              HAL_GPIO_WritePin(GPIOB, LD3_Pin, GPIO_PIN_SET);
              HAL_UART_Transmit(&huart3, (uint8_t*)json_buf, (uint16_t)json_len, HAL_MAX_DELAY);
              HAL_GPIO_WritePin(GPIOB, LD3_Pin, GPIO_PIN_RESET);
          }

          // ---- NO VLD1 HERE anymore ----

          // ---- wait out rest of the second ----
          while ((int32_t)(HAL_GetTick() - slot_deadline) < 0)
          {
              relayFSM();
              HAL_Delay(5);
          }
      }

      // -------- KMC minute summary --------
      float minute_median = 0.0f;
      float minute_avg_snr = 0.0f;
      float minute_avg_width = 0.0f;

      if (valid > 0)
      {
          for (uint32_t i = 1; i < valid; i++)
          {
              float key = vel_list[i];
              int32_t j = (int32_t)i - 1;
              while (j >= 0 && vel_list[j] > key)
              {
                  vel_list[j + 1] = vel_list[j];
                  j--;
              }
              vel_list[j + 1] = key;
          }

          if (valid & 1U) minute_median = vel_list[valid / 2U];
          else            minute_median = 0.5f * (vel_list[valid/2U - 1U] + vel_list[valid/2U]);

          minute_avg_snr   = snr_sum / (float)valid;
          minute_avg_width = wid_sum / (float)valid;
      }

      printf("Minute summary: valid=%lu, median=%.4f m/s, avgSNR=%.2f dB, avgWidth=%.4f m/s\r\n",
             (unsigned long)valid, minute_median, minute_avg_snr, minute_avg_width);

      // (Optional: Could sleep here, but user asked for continuous KMC)
  }








//      while (1)
//      {
//          // TEMP: You can keep relayFSM() if you still want relay safety logic.
//          // relayFSM();
//
//          if (half_ready || full_ready)
//          {
//              uint16_t *p = half_ready ? &adc_dma[0] : &adc_dma[DMA_LEN/2];
//              half_ready = 0;
//              full_ready = 0;
//
//              // ----- Choose ONE of the estimators -----
//              // A) Old time-domain (works without DSP)
////              float fd = estimate_fd_hz(p, IQ_PAIRS_PER_HALF, (float)FS_HZ);
//
//              // B) FFT method (only if your CMSIS-DSP linking is fixed)
//              float fd = estimate_fd_fft_hz(p, IQ_PAIRS_PER_HALF, (float)FS_HZ);
//              float fd_med = running_median_fd_push(fd);
//              float v_med  = fd_to_velocity_mps(fd_med) / cos_tilt;
//
//
//              // basic validity gate (avoid updating EMA with junk)
//              if (fd > 0.0f && isfinite(fd))
//              {
//                  if (!fd_filt_init) {
//                      fd_filt = fd;          // initialize EMA with first valid value
//                      fd_filt_init = 1;
//                  } else {
//                      fd_filt = beta * fd_filt + (1.0f - beta) * fd;
//                  }
//              }
//              // else: keep fd_filt unchanged (holds last stable value)
//
//              float v_raw  = fd_to_velocity_mps(fd)      / cos_tilt;
//              float v_ema  = fd_to_velocity_mps(fd_filt) / cos_tilt;
//
//              printf("KMC1: fd=%.2f Hz (ema=%.2f, med12=%.2f), v=%.3f m/s (ema=%.3f, med12=%.3f)\r\n",
//                     fd, fd_filt, fd_med,
//                     v_raw, v_ema, v_med);
//
//
//          }
//
//          // Small delay so UART printing doesn't hog CPU
//          HAL_Delay(5);
//      }

    /* USER CODE END WHILE */

    /* USER CODE BEGIN 3 */
  }
  /* USER CODE END 3 */


/**
  * @brief System Clock Configuration
  * @retval None
  */
void SystemClock_Config(void)
{
  RCC_OscInitTypeDef RCC_OscInitStruct = {0};
  RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};

  /** Configure LSE Drive Capability
  */
  HAL_PWR_EnableBkUpAccess();

  /** Configure the main internal regulator output voltage
  */
  __HAL_RCC_PWR_CLK_ENABLE();
  __HAL_PWR_VOLTAGESCALING_CONFIG(PWR_REGULATOR_VOLTAGE_SCALE1);

  /** Initializes the RCC Oscillators according to the specified parameters
  * in the RCC_OscInitTypeDef structure.
  */
  /* SWITCHING TO HSI for standalone reliability */
  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSI;
  RCC_OscInitStruct.HSIState = RCC_HSI_ON;
  RCC_OscInitStruct.HSICalibrationValue = RCC_HSICALIBRATION_DEFAULT;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_ON;
  RCC_OscInitStruct.PLL.PLLSource = RCC_PLLSOURCE_HSI;
  RCC_OscInitStruct.PLL.PLLM = 8;  // HSI=16MHz, /8 = 2MHz PLL input
  RCC_OscInitStruct.PLL.PLLN = 216;
  RCC_OscInitStruct.PLL.PLLP = RCC_PLLP_DIV2;
  RCC_OscInitStruct.PLL.PLLQ = 9;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK)
  {
    Error_Handler();
  }

  /** Activate the Over-Drive mode
  */
  if (HAL_PWREx_EnableOverDrive() != HAL_OK)
  {
    Error_Handler();
  }

  /** Initializes the CPU, AHB and APB buses clocks
  */
  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK|RCC_CLOCKTYPE_SYSCLK
                              |RCC_CLOCKTYPE_PCLK1|RCC_CLOCKTYPE_PCLK2;
  RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_PLLCLK;
  RCC_ClkInitStruct.AHBCLKDivider = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV4;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV2;

  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_7) != HAL_OK)
  {
    Error_Handler();
  }
}

/**
  * @brief ADC1 Initialization Function
  * @param None
  * @retval None
  */
static void MX_ADC1_Init(void)
{

  /* USER CODE BEGIN ADC1_Init 0 */

  /* USER CODE END ADC1_Init 0 */

  ADC_ChannelConfTypeDef sConfig = {0};

  /* USER CODE BEGIN ADC1_Init 1 */

  /* USER CODE END ADC1_Init 1 */

  /** Configure the global features of the ADC (Clock, Resolution, Data Alignment and number of conversion)
  */
  hadc1.Instance = ADC1;
  hadc1.Init.ClockPrescaler = ADC_CLOCK_SYNC_PCLK_DIV4;
  hadc1.Init.Resolution = ADC_RESOLUTION_12B;
  hadc1.Init.ScanConvMode = ADC_SCAN_ENABLE;
  hadc1.Init.ContinuousConvMode = DISABLE;
  hadc1.Init.DiscontinuousConvMode = DISABLE;
  hadc1.Init.ExternalTrigConvEdge = ADC_EXTERNALTRIGCONVEDGE_RISING;
  hadc1.Init.ExternalTrigConv = ADC_EXTERNALTRIGCONV_T2_TRGO;
  hadc1.Init.DataAlign = ADC_DATAALIGN_RIGHT;
  hadc1.Init.NbrOfConversion = 2;
  hadc1.Init.DMAContinuousRequests = ENABLE;
  hadc1.Init.EOCSelection = ADC_EOC_SEQ_CONV;
  if (HAL_ADC_Init(&hadc1) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure for the selected ADC regular channel its corresponding rank in the sequencer and its sample time.
  */
  sConfig.Channel = ADC_CHANNEL_0;
  sConfig.Rank = ADC_REGULAR_RANK_1;
  sConfig.SamplingTime = ADC_SAMPLETIME_144CYCLES;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }

  /** Configure for the selected ADC regular channel its corresponding rank in the sequencer and its sample time.
  */
  sConfig.Channel = ADC_CHANNEL_1;
  sConfig.Rank = ADC_REGULAR_RANK_2;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN ADC1_Init 2 */

  /* USER CODE END ADC1_Init 2 */

}

/**
  * @brief TIM2 Initialization Function
  * @param None
  * @retval None
  */
static void MX_TIM2_Init(void)
{

  /* USER CODE BEGIN TIM2_Init 0 */

  /* USER CODE END TIM2_Init 0 */

  TIM_ClockConfigTypeDef sClockSourceConfig = {0};
  TIM_MasterConfigTypeDef sMasterConfig = {0};

  /* USER CODE BEGIN TIM2_Init 1 */

  /* USER CODE END TIM2_Init 1 */
  htim2.Instance = TIM2;
  htim2.Init.Prescaler = 249;
  htim2.Init.CounterMode = TIM_COUNTERMODE_UP;
  htim2.Init.Period = 134;
  htim2.Init.ClockDivision = TIM_CLOCKDIVISION_DIV1;
  htim2.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
  if (HAL_TIM_Base_Init(&htim2) != HAL_OK)
  {
    Error_Handler();
  }
  sClockSourceConfig.ClockSource = TIM_CLOCKSOURCE_INTERNAL;
  if (HAL_TIM_ConfigClockSource(&htim2, &sClockSourceConfig) != HAL_OK)
  {
    Error_Handler();
  }
  sMasterConfig.MasterOutputTrigger = TIM_TRGO_UPDATE;
  sMasterConfig.MasterSlaveMode = TIM_MASTERSLAVEMODE_DISABLE;
  if (HAL_TIMEx_MasterConfigSynchronization(&htim2, &sMasterConfig) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN TIM2_Init 2 */

  /* USER CODE END TIM2_Init 2 */

}

/**
  * @brief USART2 Initialization Function
  * @param None
  * @retval None
  */
static void MX_USART2_UART_Init(void)
{

  /* USER CODE BEGIN USART2_Init 0 */

  /* USER CODE END USART2_Init 0 */

  /* USER CODE BEGIN USART2_Init 1 */

  /* USER CODE END USART2_Init 1 */
	huart2.Instance = USART2;
	  huart2.Init.BaudRate = 115200;
	  huart2.Init.WordLength = UART_WORDLENGTH_9B;
	  huart2.Init.StopBits = UART_STOPBITS_1;
	  huart2.Init.Parity = UART_PARITY_EVEN;
	  huart2.Init.Mode = UART_MODE_TX_RX;
	  huart2.Init.HwFlowCtl = UART_HWCONTROL_NONE;
	  huart2.Init.OverSampling = UART_OVERSAMPLING_16;
	  huart2.Init.OneBitSampling = UART_ONE_BIT_SAMPLE_DISABLE;
	  huart2.AdvancedInit.AdvFeatureInit = UART_ADVFEATURE_NO_INIT;
  if (HAL_UART_Init(&huart2) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN USART2_Init 2 */

  /* USER CODE END USART2_Init 2 */

}

/**
  * @brief USART3 Initialization Function
  * @param None
  * @retval None
  */
static void MX_USART3_UART_Init(void)
{

  /* USER CODE BEGIN USART3_Init 0 */

  /* USER CODE END USART3_Init 0 */

  /* USER CODE BEGIN USART3_Init 1 */

  /* USER CODE END USART3_Init 1 */
  huart3.Instance = USART3;
  huart3.Init.BaudRate = 460800;
  huart3.Init.WordLength = UART_WORDLENGTH_8B;
  huart3.Init.StopBits = UART_STOPBITS_1;
  huart3.Init.Parity = UART_PARITY_NONE;
  huart3.Init.Mode = UART_MODE_TX_RX;
  huart3.Init.HwFlowCtl = UART_HWCONTROL_NONE;
  huart3.Init.OverSampling = UART_OVERSAMPLING_16;
  huart3.Init.OneBitSampling = UART_ONE_BIT_SAMPLE_DISABLE;
  huart3.AdvancedInit.AdvFeatureInit = UART_ADVFEATURE_NO_INIT;
  if (HAL_UART_Init(&huart3) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN USART3_Init 2 */

  /* USER CODE END USART3_Init 2 */

}

/**
  * @brief USART6 Initialization Function
  * @param None
  * @retval None
  */
static void MX_USART6_UART_Init(void)
{

  /* USER CODE BEGIN USART6_Init 0 */

  /* USER CODE END USART6_Init 0 */

  /* USER CODE BEGIN USART6_Init 1 */

  /* USER CODE END USART6_Init 1 */
	huart6.Instance = USART6;
	  huart6.Init.BaudRate = 115200;
	  huart6.Init.WordLength = UART_WORDLENGTH_9B;
	  huart6.Init.StopBits = UART_STOPBITS_1;
	  huart6.Init.Parity = UART_PARITY_EVEN;
	  huart6.Init.Mode = UART_MODE_TX_RX;
	  huart6.Init.HwFlowCtl = UART_HWCONTROL_NONE;
	  huart6.Init.OverSampling = UART_OVERSAMPLING_16;
	  huart6.Init.OneBitSampling = UART_ONE_BIT_SAMPLE_DISABLE;
	  huart6.AdvancedInit.AdvFeatureInit = UART_ADVFEATURE_NO_INIT;
  if (HAL_UART_Init(&huart6) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN USART6_Init 2 */

  /* USER CODE END USART6_Init 2 */

}

/**
  * @brief USB_OTG_FS Initialization Function
  * @param None
  * @retval None
  */
static void MX_USB_OTG_FS_PCD_Init(void)
{

  /* USER CODE BEGIN USB_OTG_FS_Init 0 */

  /* USER CODE END USB_OTG_FS_Init 0 */

  /* USER CODE BEGIN USB_OTG_FS_Init 1 */

  /* USER CODE END USB_OTG_FS_Init 1 */
  hpcd_USB_OTG_FS.Instance = USB_OTG_FS;
  hpcd_USB_OTG_FS.Init.dev_endpoints = 6;
  hpcd_USB_OTG_FS.Init.speed = PCD_SPEED_FULL;
  hpcd_USB_OTG_FS.Init.dma_enable = DISABLE;
  hpcd_USB_OTG_FS.Init.phy_itface = PCD_PHY_EMBEDDED;
  hpcd_USB_OTG_FS.Init.Sof_enable = ENABLE;
  hpcd_USB_OTG_FS.Init.low_power_enable = DISABLE;
  hpcd_USB_OTG_FS.Init.lpm_enable = DISABLE;
  hpcd_USB_OTG_FS.Init.battery_charging_enable = ENABLE;
  hpcd_USB_OTG_FS.Init.vbus_sensing_enable = ENABLE;
  hpcd_USB_OTG_FS.Init.use_dedicated_ep1 = DISABLE;
  if (HAL_PCD_Init(&hpcd_USB_OTG_FS) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN USB_OTG_FS_Init 2 */

  /* USER CODE END USB_OTG_FS_Init 2 */

}

/**
  * Enable DMA controller clock
  */
static void MX_DMA_Init(void)
{
  /* DMA controller clock enable */
  __HAL_RCC_DMA2_CLK_ENABLE();   // for ADC
  __HAL_RCC_DMA1_CLK_ENABLE();   // ✅ ADD THIS for USART3 TX

  /* DMA interrupt init */

  /* ADC DMA2_Stream0_IRQn interrupt configuration */
  HAL_NVIC_SetPriority(DMA2_Stream0_IRQn, 0, 0);
  HAL_NVIC_EnableIRQ(DMA2_Stream0_IRQn);

  /* ✅ ADD THIS: USART3 TX uses DMA1_Stream3 */
  HAL_NVIC_SetPriority(DMA1_Stream3_IRQn, 1, 0);
  HAL_NVIC_EnableIRQ(DMA1_Stream3_IRQn);
}


/**
  * @brief GPIO Initialization Function
  * @param None
  * @retval None
  */
static void MX_GPIO_Init(void)
{
  GPIO_InitTypeDef GPIO_InitStruct = {0};
  /* USER CODE BEGIN MX_GPIO_Init_1 */

  /* USER CODE END MX_GPIO_Init_1 */

  /* GPIO Ports Clock Enable */
  __HAL_RCC_GPIOC_CLK_ENABLE();
  __HAL_RCC_GPIOH_CLK_ENABLE();
  __HAL_RCC_GPIOA_CLK_ENABLE();
  __HAL_RCC_GPIOB_CLK_ENABLE();
  __HAL_RCC_GPIOD_CLK_ENABLE();
  __HAL_RCC_GPIOG_CLK_ENABLE();

  /*Configure GPIO pin Output Level */
  HAL_GPIO_WritePin(GPIOB, LD3_Pin|LD2_Pin, GPIO_PIN_RESET);

  /*Configure GPIO pin Output Level */
  HAL_GPIO_WritePin(USB_PowerSwitchOn_GPIO_Port, USB_PowerSwitchOn_Pin, GPIO_PIN_RESET);

  /*Configure GPIO pin : USER_Btn_Pin */
  GPIO_InitStruct.Pin = USER_Btn_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_IT_RISING;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  HAL_GPIO_Init(USER_Btn_GPIO_Port, &GPIO_InitStruct);

  /*Configure GPIO pins : LD3_Pin LD2_Pin */
  GPIO_InitStruct.Pin = LD3_Pin|LD2_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(GPIOB, &GPIO_InitStruct);

  /*Configure GPIO pin : USB_PowerSwitchOn_Pin */
  GPIO_InitStruct.Pin = USB_PowerSwitchOn_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(USB_PowerSwitchOn_GPIO_Port, &GPIO_InitStruct);

  /*Configure GPIO pin : USB_OverCurrent_Pin */
  GPIO_InitStruct.Pin = USB_OverCurrent_Pin;
  GPIO_InitStruct.Mode = GPIO_MODE_INPUT;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  HAL_GPIO_Init(USB_OverCurrent_GPIO_Port, &GPIO_InitStruct);

  /* USER CODE BEGIN MX_GPIO_Init_2 */

  /* USER CODE END MX_GPIO_Init_2 */
}

/* USER CODE BEGIN 4 */
void HAL_ADC_ConvHalfCpltCallback(ADC_HandleTypeDef *hadc)
{
  if (hadc->Instance == ADC1) half_ready = 1;
}

void HAL_ADC_ConvCpltCallback(ADC_HandleTypeDef *hadc)
{
  if (hadc->Instance == ADC1) full_ready = 1;
}

/* USER CODE BEGIN 4 */
void HAL_UART_TxCpltCallback(UART_HandleTypeDef *huart)
{
    if (huart->Instance == USART3)
    {
        uart3_tx_done = 1;

        // LED indicates TX completed
        HAL_GPIO_TogglePin(GPIOB, LD3_Pin);
    }
}


void HAL_UART_ErrorCallback(UART_HandleTypeDef *huart)
{
    if (huart->Instance == USART3)
    {
        // Fast blink LD3 to show UART error happened
        for (int i = 0; i < 5; i++) {
            HAL_GPIO_TogglePin(GPIOB, LD3_Pin);
            HAL_Delay(50);
        }
        uart3_tx_done = 1; // allow retry
    }
}

/* USER CODE END 4 */


/* USER CODE END 4 */

 /* MPU Configuration */

void MPU_Config(void)
{
  MPU_Region_InitTypeDef MPU_InitStruct = {0};

  /* Disables the MPU */
  HAL_MPU_Disable();

  /** Initializes and configures the Region and the memory to be protected
  */
  MPU_InitStruct.Enable = MPU_REGION_ENABLE;
  MPU_InitStruct.Number = MPU_REGION_NUMBER0;
  MPU_InitStruct.BaseAddress = 0x0;
  MPU_InitStruct.Size = MPU_REGION_SIZE_4GB;
  MPU_InitStruct.SubRegionDisable = 0x87;
  MPU_InitStruct.TypeExtField = MPU_TEX_LEVEL0;
  MPU_InitStruct.AccessPermission = MPU_REGION_NO_ACCESS;
  MPU_InitStruct.DisableExec = MPU_INSTRUCTION_ACCESS_DISABLE;
  MPU_InitStruct.IsShareable = MPU_ACCESS_SHAREABLE;
  MPU_InitStruct.IsCacheable = MPU_ACCESS_NOT_CACHEABLE;
  MPU_InitStruct.IsBufferable = MPU_ACCESS_NOT_BUFFERABLE;

  HAL_MPU_ConfigRegion(&MPU_InitStruct);
  /* Enables the MPU */
  HAL_MPU_Enable(MPU_PRIVILEGED_DEFAULT);

}

/**
  * @brief  This function is executed in case of error occurrence.
  * @retval None
  */
void Error_Handler(void)
{
  /* USER CODE BEGIN Error_Handler_Debug */
  /* User can add his own implementation to report the HAL error return state */
  __disable_irq();
  while (1)
  {
  }
  /* USER CODE END Error_Handler_Debug */
}
#ifdef USE_FULL_ASSERT
/**
  * @brief  Reports the name of the source file and the source line number
  *         where the assert_param error has occurred.
  * @param  file: pointer to the source file name
  * @param  line: assert_param error line source number
  * @retval None
  */
void assert_failed(uint8_t *file, uint32_t line)
{
  /* USER CODE BEGIN 6 */
  /* User can add his own implementation to report the file name and line number,
     ex: printf("Wrong parameters value: file %s on line %d\r\n", file, line) */
  /* USER CODE END 6 */
}
#endif /* USE_FULL_ASSERT */
