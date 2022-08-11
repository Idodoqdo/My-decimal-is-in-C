#ifndef SRC_S21_DECIMAL_H_
#define SRC_S21_DECIMAL_H_
#include <limits.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SIGNMASK (unsigned int)0x80000000
#define SCALEMASK (unsigned int)0x00FF0000
#define SCALESHIFT 16
#define MAXSCALE 28
#define MAXINTSCALE 9

#define L 0
#define M 1
#define H 2
#define S 3
// long decimal
#define LL 0   // low long
#define ML 1   // middle long
#define HL 2   // high long
#define LHL 3  // little high long
#define MHL 4  // middle high long
#define HHL 5  // high high long
#define SL 6

// 79 228 162 514 264 337 593 543 950 335
#define DEC_MAX \
  { {0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0}, S21_NORMAL_VALUE }
// -79 228 162 514 264 337 593 543 950 335
#define DEC_MIN \
  { {0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, SIGNMASK}, S21_NORMAL_VALUE }
// 0
#define DEC_ZERO \
  { {0, 0, 0, 0}, S21_NORMAL_VALUE }
// 0.0 000 000 000 000 000 000 000 000 001
#define DEC_ZERO_ONE \
  { {1, 0, 0, 0x001C0000}, S21_NORMAL_VALUE }
// 1
#define DEC_ONE \
  { {1, 0, 0, 0}, S21_NORMAL_VALUE }
// -1
#define DEC_MINUS_ONE \
  { {1, 0, 0, SIGNMASK}, S21_NORMAL_VALUE }

enum { TRUE = 0, FALSE = 1, SUCCESS = 0, CONVERTING_ERROR = 1 };

typedef enum {
  S21_NORMAL_VALUE = 0,
  S21_INFINITY = 1,
  S21_NEGATIVE_INFINITY = 2,
  S21_NAN = 3
} value_type_t;

typedef struct {
  int bits[4];
  value_type_t value_type;
} s21_decimal;

typedef struct {
  int bits[7];
  value_type_t value_type;
} s21_long_decimal;

typedef union {
  uint32_t dw;
  float fl;
} fs;

static const uint32_t pow10Array[10] = {
    1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000};

// Internal functions
int get_bit(s21_decimal num, int pos);
int get_long_bit(s21_long_decimal num, int pos);
bool set_bit(s21_decimal* num, int pos);
bool set_long_bit(s21_long_decimal* num, int pos);
bool unset_bit(s21_decimal* num, int pos);
bool unset_long_bit(s21_long_decimal* num, int pos);
int get_scale(s21_decimal num);
int get_long_scale(s21_long_decimal num);
bool set_scale(s21_decimal* num, int scale);
bool set_long_scale(s21_long_decimal* num, int scale);
bool set_sign(s21_decimal* num, bool sign);
bool set_long_sign(s21_long_decimal* num, bool sign);
int get_sign(s21_decimal num);
int get_long_sign(s21_long_decimal num);
void dec_init(s21_decimal* num);
void long_dec_init(s21_long_decimal* num);

// Expansion of the main functions
bool s21_is_nan(s21_decimal num);
bool s21_is_inf(s21_decimal num);
bool s21_is_normal(s21_decimal num);
bool s21_is_zero(s21_decimal num);
void s21_normalize(s21_decimal* num1, s21_decimal* num2);
s21_decimal s21_normalize_round(s21_decimal original, s21_decimal normalized);
bool s21_upScale(s21_decimal* num, int* pow10Idx);
void s21_downScale(s21_decimal* num, const int* pow10Idx);
void s21_div_by_int32(s21_decimal* src, uint32_t divisor);
void s21_long_div_by_int32(s21_long_decimal* num, uint32_t divisor);
bool s21_mul_by_int32(s21_decimal* src, uint32_t multiplier);
bool s21_long_mul_by_int32(s21_long_decimal* num, uint32_t multiplier);
void s21_swap(s21_decimal* num1, s21_decimal* num2);
s21_long_decimal s21_shift_long_dec_left(s21_long_decimal num, int shift);
s21_long_decimal s21_sum_long_dec_bits(s21_long_decimal num1,
                                       s21_long_decimal num2);
s21_long_decimal s21_sub_long_dec_bits(s21_long_decimal num1,
                                       s21_long_decimal num2);
int s21_count_digits_in_number(s21_long_decimal num);
int s21_copy_decimal_to_long_decimal(s21_decimal src, s21_long_decimal* dst);
int s21_copy_long_decimal_to_decimal(s21_long_decimal src, s21_decimal* dst);
bool s21_check_is_rounding(s21_long_decimal orig, s21_long_decimal final);
s21_long_decimal s21_division(s21_long_decimal num1, s21_long_decimal num2);
int s21_bit_greater_or_equal_long(s21_long_decimal num1, s21_long_decimal num2);
int s21_bit_greater_long(s21_long_decimal num1, s21_long_decimal num2);
int s21_bit_equal_long(s21_long_decimal num1, s21_long_decimal num2);
void printbinary(s21_decimal number1);
void printlongbinary(s21_long_decimal number1);

// Arithmetic operators
s21_decimal s21_add(s21_decimal num1, s21_decimal num2);
s21_decimal s21_sub(s21_decimal num1, s21_decimal num2);
s21_decimal s21_mul(s21_decimal num1, s21_decimal num2);
s21_decimal s21_div(s21_decimal num1, s21_decimal num2);
s21_decimal s21_mod(s21_decimal num1, s21_decimal num2);

// Comparison operators
int s21_is_less(s21_decimal num1, s21_decimal num2);
int s21_is_less_or_equal(s21_decimal num1, s21_decimal num2);
int s21_is_greater(s21_decimal num1, s21_decimal num2);
int s21_is_greater_or_equal(s21_decimal num1, s21_decimal num2);
int s21_is_equal(s21_decimal num1, s21_decimal num2);
int s21_is_not_equal(s21_decimal num1, s21_decimal num2);

// Converters
int s21_from_int_to_decimal(int src, s21_decimal* dst);
int s21_from_int64_to_decimal(int64_t src, s21_decimal* dst);
int s21_from_float_to_decimal(float src, s21_decimal* dst);
int s21_from_decimal_to_int(s21_decimal src, int* dst);
int s21_from_decimal_to_int64(s21_decimal src, int64_t* dst);
int s21_from_decimal_to_float(s21_decimal src, float* dst);

// Other features
s21_decimal s21_floor(s21_decimal src);
s21_decimal s21_round(s21_decimal src);
s21_decimal s21_truncate(s21_decimal src);
s21_decimal s21_negate(s21_decimal src);
s21_decimal s21_abs(s21_decimal src);

#endif  // SRC_S21_DECIMAL_H_
