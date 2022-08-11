#include "s21_decimal.h"

// Internal functions
// Получает значение бита в pos (порядковый номер)
int get_bit(s21_decimal num, int pos) {
    return !!((1u << (pos % 32)) & num.bits[pos / 32]);
}

int get_long_bit(s21_long_decimal num, int pos) {
    return !!((1u << (pos % 32)) & num.bits[pos / 32]);
}

// Устанавливает значение бита pos в 1
bool set_bit(s21_decimal* num, int pos) {
    bool res = false;
    if (s21_is_normal(*num) && (pos >= 0 && pos <= 127)) {
        num->bits[pos / 32] |= (1u << (pos % 32));
        res = true;
    }
    return res;
}

bool set_long_bit(s21_long_decimal* num, int pos) {
    bool res = false;
    if (num->value_type == S21_NORMAL_VALUE && (pos >= 0 && pos <= 223)) {
        num->bits[pos / 32] |= (1u << (pos % 32));
        res = true;
    }
    return res;
}

// Устанавливает значение бита pos в 0, если ранее был 1
bool unset_bit(s21_decimal* num, int pos) {
    bool res = false;
    if (s21_is_normal(*num) && (pos >= 0 && pos <= 127)) {
        if (get_bit(*num, pos) == 1) {
            num->bits[pos / 32] ^= (1u << (pos % 32));
            res = true;
        }
    }
    return res;
}

bool unset_long_bit(s21_long_decimal* num, int pos) {
    bool res = false;
    if (num->value_type == S21_NORMAL_VALUE && (pos >= 0 && pos <= 223)) {
        if (get_long_bit(*num, pos) == 1) {
            num->bits[pos / 32] ^= (1u << (pos % 32));
            res = true;
        }
    }
    return res;
}

// Получает значение степени в десятичном формате
int get_scale(s21_decimal num) {
    return (num.bits[S] & SCALEMASK) >> SCALESHIFT;
}

int get_long_scale(s21_long_decimal num) {
    return (num.bits[SL] & SCALEMASK) >> SCALESHIFT;
}

// Устанавливает степень в битовом формате
bool set_scale(s21_decimal* num, int scale) {
    bool res = false;
    if (s21_is_normal(*num) && (scale <= MAXSCALE && scale >= 0)) {
        int sign = num->bits[S] & SIGNMASK;
        num->bits[S] = scale << SCALESHIFT;
        if (sign) {
            num->bits[S] |= SIGNMASK;
        }
        res = true;
    }
    return res;
}

bool set_long_scale(s21_long_decimal* num, int scale) {
    bool res = false;
    if (num->value_type == S21_NORMAL_VALUE) {
        int sign = num->bits[SL] & SIGNMASK;
        num->bits[SL] = scale << SCALESHIFT;
        if (sign) {
            num->bits[SL] |= SIGNMASK;
        }
        res = true;
    }
    return res;
}

// Устанавливает знак 1 - отрицательное, 0 - положительное
bool set_sign(s21_decimal* num, bool sign) {
    bool res = false;
    if (s21_is_inf(*num)) {
        num->value_type = (sign) ? S21_NEGATIVE_INFINITY : S21_INFINITY;
        res = true;
    } else if (s21_is_normal(*num)) {
        if (sign) {
            set_bit(num, 127);
        } else {
            unset_bit(num, 127);
        }
        res = true;
    }
    return res;
}

bool set_long_sign(s21_long_decimal* num, bool sign) {
    bool res = false;
    if (num->value_type == S21_INFINITY ||
        num->value_type == S21_NEGATIVE_INFINITY) {
        num->value_type = (sign) ? S21_NEGATIVE_INFINITY : S21_INFINITY;
        res = true;
    } else if (num->value_type == S21_NORMAL_VALUE) {
        if (sign) {
            set_long_bit(num, 223);
        } else {
            unset_long_bit(num, 223);
        }
        res = true;
    }
    return res;
}

// Получает значение знака
int get_sign(s21_decimal num) {
    bool sign = false;
    if (s21_is_inf(num)) {
        sign = (num.value_type == S21_NEGATIVE_INFINITY) ? 1 : 0;
    } else if (s21_is_normal(num)) {
        sign = get_bit(num, 127);
    }
    return sign;
}

int get_long_sign(s21_long_decimal num) {
    bool sign = false;
    if (num.value_type == S21_INFINITY ||
        num.value_type == S21_NEGATIVE_INFINITY) {
        sign = (num.value_type == S21_NEGATIVE_INFINITY) ? 1 : 0;
    } else if (num.value_type == S21_NORMAL_VALUE) {
        sign = get_long_bit(num, 223);
    }
    return sign;
}

// Инициализации структуры или обнуление decimal
void dec_init(s21_decimal* num) {
    num->bits[L] = 0;
    num->bits[M] = 0;
    num->bits[H] = 0;
    num->bits[S] = 0;
    num->value_type = S21_NORMAL_VALUE;
}

// Инициализации структуры или обнуление long decimal
void long_dec_init(s21_long_decimal* num) {
    for (int i = 0; i < 7; i++) {
        num->bits[i] = 0;
    }
    num->value_type = S21_NORMAL_VALUE;
}

// Expansion of the main functions
// Проверка что decimal = NAN
bool s21_is_nan(s21_decimal num) { return (num.value_type == S21_NAN); }

// Проверка что decimal любой вариант бесконечности
bool s21_is_inf(s21_decimal num) {
    return (num.value_type == S21_INFINITY) ||
           (num.value_type == S21_NEGATIVE_INFINITY);
}

// Проверка что decimal корректный
bool s21_is_normal(s21_decimal num) {
    return (num.value_type == S21_NORMAL_VALUE);
}

// Проверка что decimal пустой и корректный, не учитывая степень
bool s21_is_zero(s21_decimal num) {
    return s21_is_normal(num) && !num.bits[L] && !num.bits[M] && !num.bits[H];
}

// Выравнивание степени двух decimal
void s21_normalize(s21_decimal* num1, s21_decimal* num2) {
    // -0 -> 0
    if (s21_is_zero(*num1)) *num1 = s21_abs(*num1);
    if (s21_is_zero(*num2)) *num2 = s21_abs(*num2);

    int scale1 = get_scale(*num1), scale2 = get_scale(*num2);
    if (scale1 != scale2) {
        bool rounding = false;
        // Temporary number storage, for rounding
        s21_decimal TNS1 = *num1, TNS2 = *num2;
        s21_decimal* mul = (scale1 > scale2) ? num2 : num1;
        s21_decimal* div = (scale1 > scale2) ? num1 : num2;
        int diff_scale = (scale1 > scale2) ? scale1 - scale2 : scale2 - scale1;
        while (diff_scale > 0) {
            int pow10Idx = (diff_scale > MAXINTSCALE) ? MAXINTSCALE : diff_scale;
            if (!s21_upScale(mul, &pow10Idx)) {
                s21_downScale(div, &pow10Idx);
                rounding = true;
            }
            diff_scale -= pow10Idx;
        }
        // Rounding if reduced precision
        if (rounding) {
            *num1 = s21_normalize_round(TNS1, *num1);
            *num2 = s21_normalize_round(TNS2, *num2);
        }
    }
}

// Округляет decimal у которого была уменьшена степень
s21_decimal s21_normalize_round(s21_decimal original, s21_decimal normalized) {
    s21_decimal res = normalized;
    int scale = get_scale(normalized);

    if (get_scale(original) > scale) {
        bool sign = get_sign(normalized);  // save sign
        original = s21_abs(original);
        normalized = s21_abs(normalized);

        s21_decimal half = {{5, 0, 0, 0x00010000}, S21_NORMAL_VALUE};  // 0.5
        s21_decimal diff = s21_sub(original, normalized);              // remainder
        if (s21_is_zero(diff) == 0) {                                  // not zero
            set_scale(&diff, (get_scale(original) - scale));
            s21_normalize(&diff, &half);
            if (s21_is_greater_or_equal(diff, half) == TRUE) {
                s21_decimal zero_one = DEC_ZERO_ONE;
                set_scale(&zero_one, scale);
                res = s21_add(normalized, zero_one);
            }
        }
        set_sign(&res, sign);  // restore sign
    }
    return res;
}

// check overflow
// Увеличивает степень decimal путем умножения, с проверкой на переполнение
bool s21_upScale(s21_decimal* num, int* pow10Idx) {
    bool result = false;
    if (s21_mul_by_int32(num, pow10Array[*pow10Idx])) {
        set_scale(num, get_scale(*num) + *pow10Idx);
        result = true;
    } else {
        if (*pow10Idx > 1) {
            (*pow10Idx)--;
            if (s21_upScale(num, pow10Idx)) {
                result = true;
            } else {
                result = false;
            }
        } else {
            result = false;
        }
    }
    return result;
}

// uncheck overflow
// Уменьшает степень decimal путем деления, без проверки на переполнение
void s21_downScale(s21_decimal* num, const int* pow10Idx) {
    s21_div_by_int32(num, pow10Array[*pow10Idx]);
    set_scale(num, get_scale(*num) - *pow10Idx);
}

// Деление decimal на беззнаковое целое число, в пределах формата int,
// без проверки на переполнение
void s21_div_by_int32(s21_decimal* num, uint32_t divisor) {
    uint32_t remainder = 0;
    uint64_t tmp;
    if (num->bits[H] != 0) {
        tmp = (uint32_t)num->bits[H];
        num->bits[H] = (int)((uint32_t)(tmp / divisor));
        remainder = (uint32_t)(tmp % divisor);
    }
    if (num->bits[M] != 0 || remainder != 0) {
        tmp = ((uint64_t)remainder << 32) | (uint32_t)num->bits[M];
        num->bits[M] = (int)((uint32_t)(tmp / divisor));
        remainder = (uint32_t)(tmp % divisor);
    }
    if (num->bits[L] != 0 || remainder != 0) {
        tmp = ((uint64_t)remainder << 32) | (uint32_t)num->bits[L];
        num->bits[L] = (int)((uint32_t)(tmp / divisor));
    }
}

// Деление long_decimal на беззнаковое целое число, в пределах формата int,
// без проверки на переполнение
void s21_long_div_by_int32(s21_long_decimal* num, uint32_t divisor) {
    uint32_t remainder = 0;
    uint64_t tmp;
    for (int i = HHL; i >= 0; i--) {
        if (i == HHL && num->bits[i] != 0) {
            tmp = (uint32_t)num->bits[i];
            num->bits[i] = (int)((uint32_t)(tmp / divisor));
            remainder = (uint32_t)(tmp % divisor);
        } else if (i < HHL && (num->bits[i] != 0 || remainder != 0)) {
            tmp = ((uint64_t)remainder << 32) | (uint32_t)num->bits[i];
            num->bits[i] = (int)((uint32_t)(tmp / divisor));
            remainder = (uint32_t)(tmp % divisor);
        }
    }
}

// Умножение decimal на беззнаковое целое число, в пределах формата int,
// с проверкой на переполнение
bool s21_mul_by_int32(s21_decimal* num, uint32_t multiplier) {
    bool result = false;
    s21_decimal buffer = *num;
    uint32_t carry = 0;
    for (int i = L; i <= H; i++) {
        uint64_t tmp = (uint64_t)((uint32_t)buffer.bits[i]) * multiplier + carry;
        carry = tmp / 0x100000000;
        buffer.bits[i] = (int)(tmp % 0x100000000);
    }
    if (carry > 0) {
        result = false;
    } else {
        *num = buffer;
        result = true;
    }
    return result;
}

bool s21_long_mul_by_int32(s21_long_decimal* num, uint32_t multiplier) {
    bool result = false;
    s21_long_decimal buffer = *num;
    uint32_t carry = 0;
    for (int i = LL; i <= HHL; i++) {
        uint64_t tmp = (uint64_t)((uint32_t)buffer.bits[i]) * multiplier + carry;
        carry = tmp / 0x100000000;
        buffer.bits[i] = (int)(tmp % 0x100000000);
    }
    if (carry > 0) {
        result = false;
    } else {
        *num = buffer;
        result = true;
    }
    return result;
}

// Swap values without checking
// Меняет значения переменных местами
void s21_swap(s21_decimal* num1, s21_decimal* num2) {
    s21_decimal tmp = *num1;
    *num1 = *num2;
    *num2 = tmp;
}

// Умножение на 2 в степени n, методом сдвига битов для s21_long_decimal
s21_long_decimal s21_shift_long_dec_left(s21_long_decimal num, int shift) {
    s21_long_decimal res = {{0}, S21_NORMAL_VALUE};
    if (num.value_type == S21_NORMAL_VALUE) {
        for (int i = 191; i >= 0; i--) {
            if ((i > 191 - shift) && get_long_bit(num, i)) {
                long_dec_init(&res);
                res.value_type = S21_INFINITY;
                break;
            } else if (i >= shift) {
                if (get_long_bit(num, i - shift) == 1) {
                    set_long_bit(&res, i);
                } else {
                    unset_long_bit(&res, i);
                }
            }
        }
    } else {
        res.value_type = num.value_type;
    }
    return res;
}

// Суммирует биты num1 и num2
s21_long_decimal s21_sum_long_dec_bits(s21_long_decimal num1,
                                       s21_long_decimal num2) {
    int carry = 0;
    s21_long_decimal res = {{0}, S21_NORMAL_VALUE};
    for (int i = 0; i < 192; i++) {
        int bit_num1 = get_long_bit(num1, i);
        int bit_num2 = get_long_bit(num2, i);
        if (bit_num1 ^ bit_num2 ^ carry) {
            set_long_bit(&res, i);
        }
        if ((bit_num1 + bit_num2 + carry) > 1) {
            carry = 1;
        } else {
            carry = 0;
        }
    }

    if (carry) {
        res.value_type = S21_INFINITY;
    }
    return res;
}

// Вычитает биты num1 b num2
s21_long_decimal s21_sub_long_dec_bits(s21_long_decimal num1,
                                       s21_long_decimal num2) {
    s21_long_decimal result = {{0}, S21_NORMAL_VALUE};
    int carry = 0;
    for (int i = 0; i < 192; i++) {  // substraction
        int bit_num1 = get_long_bit(num1, i);
        int bit_num2 = get_long_bit(num2, i);
        if (carry == 0) {
            if (bit_num1 == 0 && bit_num2 == 1) {
                carry = 1;
                set_long_bit(&result, i);
            } else if (bit_num1 ^ bit_num2) {
                set_long_bit(&result, i);
            }
        } else {
            if (bit_num1 == 1 && bit_num2 == 0) {
                carry = 0;
            } else if (bit_num1 == 1 && bit_num2 == 1) {
                set_long_bit(&result, i);
            } else if (bit_num1 == 0 && bit_num2 == 1) {
                unset_long_bit(&result, i);
            } else if (bit_num1 == 0 && bit_num2 == 0) {
                set_long_bit(&result, i);
            }
        }
    }  // end for

    if (carry) {
        result.value_type = S21_INFINITY;
    }
    return result;
}

// Считает разряды числа путем деления на 10
int s21_count_digits_in_number(s21_long_decimal num) {
    uint64_t tmp;
    int count = 0;
    while (num.bits[0] != 0) {
        uint32_t remainder = 0;
        for (int i = HHL; i >= LL; i--) {
            if (i == HHL && num.bits[i] != 0) {
                tmp = (uint32_t)num.bits[i];
                num.bits[i] = (int)((uint32_t)(tmp / 10));
                remainder = (uint32_t)(tmp % 10);
            } else if (i < HHL && (num.bits[i] != 0 || remainder != 0)) {
                tmp = ((uint64_t)remainder << 32) | (uint32_t)num.bits[i];
                num.bits[i] = (int)((uint32_t)(tmp / 10));
                remainder = (uint32_t)(tmp % 10);
            }
        }
        count++;
    }
    return count;
}

// Перевести число из decimal в long decimal
int s21_copy_decimal_to_long_decimal(s21_decimal src, s21_long_decimal* dst) {
    int res = CONVERTING_ERROR;
    if (dst) {
        long_dec_init(dst);
        if (src.value_type == S21_NORMAL_VALUE) {
            for (int i = L; i <= H; i++) {
                dst->bits[i] = src.bits[i];
            }
            dst->bits[SL] = src.bits[S];
            res = SUCCESS;
        } else {
            dst->value_type = src.value_type;
        }
    }
    return res;
}

// Перевести число из long decimal в decimal
int s21_copy_long_decimal_to_decimal(s21_long_decimal src, s21_decimal* dst) {
    int res = CONVERTING_ERROR;
    if (dst) {
        dec_init(dst);
        int sign = get_long_sign(src);
        if (src.value_type == S21_NORMAL_VALUE) {
            set_long_sign(&src, 0);
            // check overflow
            bool overflow = false;
            int scale = get_long_scale(src);  // save scale
            set_long_scale(&src, 0);          // clear scale
            int count_integer = s21_count_digits_in_number(src);
            int whole = count_integer - scale;
            if (whole > 29) {
                overflow = true;
            } else if (whole < 1) {  // integer is zero
                whole = 1;
            }
            // Preparing the result
            if (!overflow) {
                bool is_rounding = false;
                if (count_integer > 29 || scale > MAXSCALE) {  // rounding required
                    s21_long_decimal tmp;
                    int diff = scale - (29 - whole);
                    scale = 29 - whole;  // new scale
                    do {
                        int pow10Idx = (diff > MAXINTSCALE) ? MAXINTSCALE : diff;
                        tmp = src;
                        s21_long_div_by_int32(&src, pow10Array[pow10Idx]);
                        diff -= pow10Idx;
                        if (!diff && (src.bits[HHL] || src.bits[MHL] ||
                                      src.bits[LHL])) {  // overflow
                            diff++;
                            scale--;
                        }
                    } while (diff > 0);
                    is_rounding = s21_check_is_rounding(tmp, src);
                }
                // save result
                for (int i = L; i <= H; i++) {
                    dst->bits[i] = src.bits[i];
                }
                if (is_rounding) {
                    s21_decimal one = DEC_ONE;
                    *dst = s21_add(*dst, one);
                }
                set_scale(dst, scale);
                set_sign(dst, sign);
                res = SUCCESS;
            } else {
                dst->value_type = sign ? S21_NEGATIVE_INFINITY : S21_INFINITY;
                res = SUCCESS;
            }
        } else {
            dst->value_type = sign ? S21_NEGATIVE_INFINITY : S21_INFINITY;
            res = SUCCESS;
        }
    }
    return res;
}

bool s21_check_is_rounding(s21_long_decimal orig, s21_long_decimal final) {
    bool res = false;
    int diff =
        s21_count_digits_in_number(orig) - s21_count_digits_in_number(final);
    if (s21_long_mul_by_int32(&final, pow10Array[diff])) {
        s21_long_decimal result = s21_sub_long_dec_bits(orig, final);
        if (result.value_type == S21_NORMAL_VALUE) {
            int count_digit = s21_count_digits_in_number(result);
            if (count_digit == diff) {
                if (count_digit > 1) {
                    s21_long_div_by_int32(&result, pow10Array[count_digit - 1]);
                }
                if (result.bits[LL] >= 5 && result.bits[LL] <= 9) {
                    res = true;
                }
            }
        }
    }
    return res;
}

s21_long_decimal s21_division(s21_long_decimal num1, s21_long_decimal num2) {
    s21_long_decimal dividend = {{0}, S21_NORMAL_VALUE};
    s21_long_decimal result = {{0}, S21_NORMAL_VALUE};
    s21_long_decimal zero = {{0}, S21_NORMAL_VALUE};
    s21_long_decimal one = {{1, 0, 0, 0, 0, 0, 0}, S21_NORMAL_VALUE};
    // whole part
    int shift = 0, flags = 0;
    for (int i = 191; i >= 0; i--) {
        dividend = s21_shift_long_dec_left(dividend, 1);
        if (get_long_bit(num1, i) == 1) {
            dividend = s21_sum_long_dec_bits(dividend, one);
        }
        if (s21_bit_greater_or_equal_long(dividend, num2) == TRUE) {
            if (flags == 1) {
                result = s21_shift_long_dec_left(result, 1);
            }
            set_long_bit(&result, 0);
            dividend = s21_sub_long_dec_bits(dividend, num2);
            if (flags == 0) {
                flags = 1;
            }
        } else if (s21_bit_greater_or_equal_long(dividend, num2) == FALSE &&
                   flags == 1) {
            result = s21_shift_long_dec_left(result, 1);
        }
        if (flags == 1) {
            shift++;
        }
    }
    // Fraction
    if (!result.bits[HHL] && !result.bits[MHL] && !result.bits[LHL]) {
        int scale = 0;
        while (s21_bit_equal_long(dividend, zero) == FALSE && scale <= MAXSCALE &&
               result.bits[HHL] < INT32_MAX) {
            while (s21_bit_greater_or_equal_long(dividend, num2) == FALSE &&
                   scale <= MAXSCALE) {
                s21_long_mul_by_int32(&dividend, 10);
                s21_long_mul_by_int32(&result, 10);
                scale++;
            }
            int count_sub = 0;
            while (s21_bit_greater_or_equal_long(dividend, num2) == TRUE) {
                dividend = s21_sub_long_dec_bits(dividend, num2);
                count_sub++;
            }
            s21_long_decimal tmp = {{count_sub, 0, 0, 0, 0, 0, 0}, S21_NORMAL_VALUE};
            result = s21_sum_long_dec_bits(result, tmp);
        }
        set_long_scale(&result, scale);
    } else {
        long_dec_init(&result);
        result.value_type = S21_INFINITY;
    }
    return result;
}

int s21_bit_greater_or_equal_long(s21_long_decimal num1,
                                  s21_long_decimal num2) {
    int res = FALSE;
    if ((s21_bit_equal_long(num1, num2) == TRUE) ||
        (s21_bit_greater_long(num1, num2) == TRUE)) {
        res = TRUE;
    }
    return res;
}

int s21_bit_greater_long(s21_long_decimal num1, s21_long_decimal num2) {
    int res = FALSE;
    for (int i = HHL; i >= LL; i--) {
        if ((uint32_t)num1.bits[i] > (uint32_t)num2.bits[i]) {
            res = TRUE;
            break;
        } else if ((uint32_t)num1.bits[i] < (uint32_t)num2.bits[i]) {
            break;
        }
    }
    return res;
}

int s21_bit_equal_long(s21_long_decimal num1, s21_long_decimal num2) {
    int res = TRUE;
    for (int i = HHL; i >= LL; i--) {
        if (num1.bits[i] != num2.bits[i]) {
            res = FALSE;
            break;
        }
    }
    return res;
}

#ifdef DEBUG
void printbinary(s21_decimal number1) {
    for (int i = 127; i >= 0; i--) {
        if (i % 32 == 31) printf(" ");
        if (i == 111 || i == 118) printf(" ");
        printf("%d", get_bit(number1, i));
    }
    printf("\n");
}

void printlongbinary(s21_long_decimal number1) {
    for (int i = 223; i >= 0; i--) {
        if (i % 32 == 31) printf(" ");
        if (i == 207 || i == 214) printf(" ");
        printf("%d", get_long_bit(number1, i));
    }
    printf("\n");
}
#endif

// Arithmetic operators
s21_decimal s21_add(s21_decimal num1, s21_decimal num2) {
    s21_decimal result = DEC_ZERO;
    if (s21_is_nan(num1) || s21_is_nan(num2)) {  // NAN
        result.value_type = S21_NAN;
    } else if (s21_is_inf(num1) &&
               s21_is_inf(num2)) {  // addition of two infinities
        result.value_type = S21_NAN;
    } else if (s21_is_inf(num1)) {
        result.value_type = num1.value_type;
    } else if (s21_is_inf(num2)) {
        result.value_type = num2.value_type;
    } else if (s21_is_zero(num1) && get_scale(num1) == 0) {
        // if one of the values is zero we return the second one without
        // calculations
        result = num2;
    } else if (s21_is_zero(num2) && get_scale(num2) == 0) {
        result = num1;
    } else {
        s21_normalize(&num1, &num2);
        int sign1 = get_sign(num1), sign2 = get_sign(num2);
        // Convert number to modulo
        num1 = s21_abs(num1);
        num2 = s21_abs(num2);
        if (sign1 == sign2) {  // addition
            int carry = 0;     // the remainder of the number to carry
            int scale = get_scale(num1);
            for (int i = 0; i < 96; i++) {
                int bit_num1 = get_bit(num1, i);
                int bit_num2 = get_bit(num2, i);
                if (bit_num1 ^ bit_num2 ^ carry) {
                    set_bit(&result, i);
                }
                if ((bit_num1 + bit_num2 + carry) > 1) {
                    carry = 1;
                } else {
                    carry = 0;
                }
            }
            if (carry) {  // overflow
                // change scale??
                // 5.78.. + 4.64.. = 10.4..
                if (scale > 0) {
                    scale--;
                } else {
                    dec_init(&result);
                    result.value_type = sign1 ? S21_NEGATIVE_INFINITY : S21_INFINITY;
                }
            }
            set_sign(&result, sign1);
            set_scale(&result, scale);
        } else {                                             // subtraction
            if (s21_is_less_or_equal(num1, num2) == TRUE) {  // num1 <= num2
                if (s21_is_not_equal(num1, num2) ==
                    TRUE) {  // num1 != num2 else result zero
                    result = s21_sub(num2, num1);
                    set_sign(&result, sign2);
                }
            } else {  // num1 > num2
                result = s21_sub(num1, num2);
                set_sign(&result, sign1);
            }
        }
    }
    return result;
}

s21_decimal s21_sub(s21_decimal num1, s21_decimal num2) {
    s21_decimal result = DEC_ZERO;
    if (s21_is_nan(num1) || s21_is_nan(num2)) {  // NAN
        result.value_type = S21_NAN;
    } else if (s21_is_inf(num1) &&
               s21_is_inf(num2)) {  // subtraction of two infinities
        if (num1.value_type == num2.value_type) {
            result.value_type = S21_NAN;
        } else {
            result.value_type = num1.value_type;
        }
    } else if (s21_is_inf(num1)) {
        result.value_type = num1.value_type;
    } else if (s21_is_inf(num2)) {
        result.value_type = num2.value_type;
        result = s21_negate(result);
    } else if (s21_is_zero(num1)) {
        // if one of the values is zero we return the second one without
        // calculations
        s21_normalize(&num1, &num2);
        result = num2;
        if (!s21_is_zero(result)) {
            set_sign(&result, !get_sign(num2));
        }
    } else if (s21_is_zero(num2)) {
        s21_normalize(&num1, &num2);
        result = num1;
        set_sign(&result, get_sign(num1));
    } else {
        int sign1 = get_sign(num1), sign2 = get_sign(num2);
        if (sign1 == sign2) {  // subtraction
            if (sign1 & sign2) {
                num1 = s21_abs(num1);
                num2 = s21_abs(num2);
            }
            if (s21_is_not_equal(num1, num2) ==
                TRUE) {                                 // num1 != num2 else result zero
                if (s21_is_less(num1, num2) == TRUE) {  // num1 < num2
                    s21_swap(&num1, &num2);
                    sign1 = !(sign1);
                }
                s21_long_decimal long_num1, long_num2, long_sub;
                // conversion
                s21_copy_decimal_to_long_decimal(num1, &long_num1);
                s21_copy_decimal_to_long_decimal(num2, &long_num2);
                // Normalize long decimal
                int scale1 = get_long_scale(long_num1),
                    scale2 = get_long_scale(long_num2);
                if (scale1 != scale2) {
                    int diff_scale = abs(scale1 - scale2);
                    s21_long_decimal* upScale =
                        (scale1 > scale2) ? &long_num2 : &long_num1;
                    while (diff_scale > 0) {
                        int pow10Idx =
                            (diff_scale > MAXINTSCALE) ? MAXINTSCALE : diff_scale;
                        s21_long_mul_by_int32(upScale, pow10Array[pow10Idx]);
                        diff_scale -= pow10Idx;
                    }
                }
                // Clear scale
                set_scale(&num1, 0);
                set_scale(&num2, 0);
                // action
                long_sub = s21_sub_long_dec_bits(long_num1, long_num2);
                set_long_sign(&long_sub, sign1);
                int scale = (scale1 > scale2) ? scale1 : scale2;
                set_long_scale(&long_sub, scale);
                if (s21_copy_long_decimal_to_decimal(long_sub, &result) ==
                    CONVERTING_ERROR) {
                    dec_init(&result);
                    result.value_type = sign1 ? S21_NEGATIVE_INFINITY : S21_INFINITY;
                }
            }
        } else {  // addition
            num1 = s21_abs(num1);
            num2 = s21_abs(num2);
            result = s21_add(num1, num2);
            if (sign1) {
                result = s21_negate(result);
            }
        }
    }
    return result;
}
s21_decimal s21_mul(s21_decimal num1, s21_decimal num2) {
    s21_decimal result = DEC_ZERO;
    s21_decimal one = DEC_ONE;
    if ((s21_is_inf(num1) && s21_is_zero(num2)) ||
        (s21_is_inf(num2) && s21_is_zero(num1))) {
        result.value_type = S21_NAN;
    } else if (s21_is_nan(num1) || s21_is_nan(num2)) {
        result.value_type = S21_NAN;
    } else if (s21_is_inf(num1) && s21_is_inf(num2)) {
        result.value_type = S21_NAN;
    } else if (s21_is_inf(num1) || s21_is_inf(num2)) {
        if (get_sign(num1) == get_sign(num2)) {
            result.value_type = S21_INFINITY;
        } else {
            result.value_type = S21_NEGATIVE_INFINITY;
        }
    } else if (s21_is_equal(num2, one) == TRUE) {
        result = num1;
        set_sign(&result, !(get_sign(num1) == get_sign(num2)));
    } else if (s21_is_zero(num1)) {
        int scale = get_scale(num1);
        if (scale > 0) {
            scale = scale + get_scale(num2);
            scale = (scale > MAXSCALE) ? MAXSCALE : scale;
            set_scale(&result, scale);
        }
    } else if (s21_is_zero(num2) == 0) {  // num2 not zero else result zero
        bool sign = (get_sign(num1) == get_sign(num2)) ? 0 : 1;
        int scale = get_scale(num1) + get_scale(num2);
        s21_long_decimal long_num1, long_num2, long_mul = {{0}, S21_NORMAL_VALUE};
        // Clear scale & sign
        if (scale > 0) {
            set_scale(&num1, 0);
            set_scale(&num2, 0);
        }
        if (get_sign(num1) == 1 || get_sign(num2) == 1) {
            num1 = s21_abs(num1);
            num2 = s21_abs(num2);
        }
        // conversion
        s21_copy_decimal_to_long_decimal(num1, &long_num1);
        s21_copy_decimal_to_long_decimal(num2, &long_num2);
        // action
        for (int i = 0; i < 192; i++) {
            s21_long_decimal tmp = s21_shift_long_dec_left(long_num1, i);
            if (get_long_bit(long_num2, i)) {
                long_mul = s21_sum_long_dec_bits(long_mul, tmp);
            }
        }
        set_long_scale(&long_mul, scale);
        set_long_sign(&long_mul, sign);
        if (s21_copy_long_decimal_to_decimal(long_mul, &result) ==
            CONVERTING_ERROR) {
            dec_init(&result);
            result.value_type = sign ? S21_NEGATIVE_INFINITY : S21_INFINITY;
        }
    }
    return result;
}

s21_decimal s21_div(s21_decimal num1, s21_decimal num2) {
    s21_decimal result = DEC_ZERO;
    s21_decimal one = DEC_ONE;
    if (s21_is_inf(num1) && s21_is_inf(num2)) {
        result.value_type = S21_NAN;
    } else if (s21_is_nan(num1) || s21_is_nan(num2)) {
        result.value_type = S21_NAN;
    } else if (s21_is_zero(num1) && s21_is_zero(num2)) {
        result.value_type = S21_NAN;
    } else if (s21_is_zero(num2)) {
        result.value_type = get_sign(num1) ? S21_NEGATIVE_INFINITY : S21_INFINITY;
    } else if (s21_is_inf(num1)) {
        if (get_sign(num1) == get_sign(num2)) {
            result.value_type = S21_INFINITY;
        } else {
            result.value_type = S21_NEGATIVE_INFINITY;
        }
    } else if (s21_is_zero(num1)) {
        int scale = get_scale(num1);
        if (scale > 0) {
            scale = scale - get_scale(num2);
            scale = (scale > 0) ? scale : 0;
            set_scale(&result, scale);
        }
    } else if (s21_is_equal(num2, one) == TRUE) {
        result = num1;
        set_sign(&result, !(get_sign(num1) == get_sign(num2)));
    } else if (s21_is_inf(num2) == 0) {  // else result zero
        bool sign = (get_sign(num1) == get_sign(num2)) ? 0 : 1;
        if (s21_is_equal(num1, num2) ==
            TRUE) {  // num1 == num2 the result of the division will be one
            result = one;
            set_sign(&result, sign);
        } else {
            s21_long_decimal long_num1, long_num2, long_div;
            // conversion
            s21_copy_decimal_to_long_decimal(num1, &long_num1);
            s21_copy_decimal_to_long_decimal(num2, &long_num2);
            // Normalize long decimal
            int scale1 = get_long_scale(long_num1),
                scale2 = get_long_scale(long_num2);
            if (scale1 != scale2) {
                int diff_scale = abs(scale1 - scale2);
                s21_long_decimal* upScale = (scale1 > scale2) ? &long_num2 : &long_num1;
                while (diff_scale > 0) {
                    int pow10Idx = (diff_scale > MAXINTSCALE) ? MAXINTSCALE : diff_scale;
                    s21_long_mul_by_int32(upScale, pow10Array[pow10Idx]);
                    diff_scale -= pow10Idx;
                }
            }
            // Clear scale & sign
            if (get_sign(num1) == 1) num1 = s21_abs(num1);
            if (get_sign(num2) == 1) num2 = s21_abs(num2);
            if (get_scale(num1) > 0) set_scale(&num1, 0);
            if (get_scale(num2) > 0) set_scale(&num2, 0);
            // action
            long_div = s21_division(long_num1, long_num2);
            set_long_sign(&long_div, sign);
            if (s21_copy_long_decimal_to_decimal(long_div, &result) ==
                CONVERTING_ERROR) {
                dec_init(&result);
                result.value_type = sign ? S21_NEGATIVE_INFINITY : S21_INFINITY;
            } else {  // removing trailing zeros
                int exp = get_scale(result);
                if (s21_is_normal(result) && !s21_is_zero(result) && exp) {
                    s21_decimal tmp = DEC_ONE;
                    do {
                        tmp = result;
                        set_scale(&tmp, 1);
                        tmp = s21_sub(tmp, s21_truncate(tmp));
                        if (tmp.bits[L] == 0) {
                            s21_div_by_int32(&result, 10);
                            exp--;
                        }
                    } while (tmp.bits[L] == 0 && exp > 0);
                    set_scale(&result, exp);
                }
            }
        }
    }
    return result;
}

s21_decimal s21_mod(s21_decimal num1, s21_decimal num2) {
    s21_decimal result = DEC_ZERO;
    if (s21_is_nan(num1) || s21_is_nan(num2)) {
        result.value_type = S21_NAN;
    } else if (s21_is_inf(num1) || s21_is_zero(num2)) {
        result.value_type = S21_NAN;
    } else if (s21_is_normal(num1) && s21_is_inf(num2)) {
        result = num1;
    } else {
        s21_decimal tmp = s21_div(num1, num2);
        if (s21_is_normal(tmp)) {
            tmp = s21_truncate(tmp);
            result = s21_sub(num1, s21_mul(tmp, num2));
        } else {
            set_scale(&result, get_scale(num2));
        }
    }
    return result;
}

// Comparison operators
// num1 < num2
int s21_is_less(s21_decimal num1, s21_decimal num2) {
    int res = FALSE;  // default
    if (num1.value_type == S21_NEGATIVE_INFINITY &&
        num2.value_type == S21_INFINITY) {
        res = TRUE;
    } else if ((num1.value_type == S21_NEGATIVE_INFINITY &&
                s21_is_normal(num2)) ||
               (num2.value_type == S21_INFINITY && s21_is_normal(num1))) {
        res = TRUE;
    } else if (s21_is_zero(num1) && s21_is_zero(num2)) {  // not zero
        res = FALSE;
    } else if (s21_is_normal(num1) && s21_is_normal(num2)) {
        s21_normalize(&num1, &num2);
        int sign_num1 = get_sign(num1), sign_num2 = get_sign(num2);
        if (sign_num1 == 1 && sign_num2 == 0) {  // negative num1 less positive num2
            res = TRUE;
        } else if (sign_num1 == sign_num2) {
            if (s21_is_not_equal(num1, num2) == TRUE) {
                // Comparing only integer parts of floating point numbers
                bool remainder_comparison = true;
                if (get_scale(num1) > 0) {
                    s21_decimal tmp1 = s21_truncate(num1);
                    s21_decimal tmp2 = s21_truncate(num2);
                    if (s21_is_not_equal(tmp1, tmp2) == TRUE) {
                        res = s21_is_less(tmp1, tmp2);
                        remainder_comparison = false;
                    }
                }

                // compare integers or remainder
                if (remainder_comparison) {
                    bool bits_compare = true;
                    if (num1.bits[H] == 0 && num2.bits[H] == 0) {
                        int64_t number1, number2;
                        set_scale(&num1, 0);
                        set_scale(&num2, 0);
                        if (s21_from_decimal_to_int64(num1, &number1) == SUCCESS) {
                            if (s21_from_decimal_to_int64(num2, &number2) == SUCCESS) {
                                res = !((uint64_t)number1 < (uint64_t)number2);
                                bits_compare = false;
                            }
                        }
                    }
                    if (bits_compare) {
                        res = FALSE;
                        if ((uint32_t)num1.bits[H] < (uint32_t)num2.bits[H]) {
                            res = TRUE;
                        } else if ((uint32_t)num1.bits[H] == (uint32_t)num2.bits[H]) {
                            if ((uint32_t)num1.bits[M] < (uint32_t)num2.bits[M]) {
                                res = TRUE;
                            } else if ((uint32_t)num1.bits[M] == (uint32_t)num2.bits[M]) {
                                if ((uint32_t)num1.bits[L] < (uint32_t)num2.bits[L]) {
                                    res = TRUE;
                                }
                            }
                        }
                        if (get_sign(num1) == get_sign(num2) && get_sign(num1) == 1) {
                            res = !res;
                        }
                    }
                }
            }
        }
    }
    return res;
}

// num1 <= num2
int s21_is_less_or_equal(s21_decimal num1, s21_decimal num2) {
    int res = s21_is_equal(num1, num2);
    if (res == FALSE) {
        res = s21_is_less(num1, num2);
    }
    return res;
}

// num1 > num2
int s21_is_greater(s21_decimal num1, s21_decimal num2) {
    int res = TRUE;
    if (num2.value_type == S21_INFINITY && s21_is_zero(num1)) {
        res = FALSE;
    } else if (num1.value_type == S21_NEGATIVE_INFINITY ||
               num2.value_type == S21_INFINITY) {
        res = FALSE;
    } else if (s21_is_nan(num1) || s21_is_nan(num2)) {
        res = FALSE;
    } else if (s21_is_equal(num1, num2) == TRUE) {
        res = FALSE;
    } else {
        res = !s21_is_less(num1, num2);
    }
    return res;
}

// num1 >= num2
int s21_is_greater_or_equal(s21_decimal num1, s21_decimal num2) {
    int res = s21_is_equal(num1, num2);
    if (res == FALSE) {
        res = s21_is_greater(num1, num2);
    }
    return res;
}

// num1 == num2
int s21_is_equal(s21_decimal num1, s21_decimal num2) {
    int res = FALSE;
    if (s21_is_normal(num1) && s21_is_normal(num2)) {
        s21_normalize(&num1, &num2);
        if (get_sign(num1) == get_sign(num2)) {
            int coincidences = 0;
            for (int i = L; i <= H; i++) {
                if (num1.bits[i] == num2.bits[i]) {
                    coincidences++;
                } else {
                    break;
                }
            }
            if (coincidences == 3) {
                res = TRUE;
            }
        }
    } else if (num1.value_type == num2.value_type && !s21_is_nan(num1)) {
        res = TRUE;
    }
    return res;
}

// num1 != num2
int s21_is_not_equal(s21_decimal num1, s21_decimal num2) {
    return !s21_is_equal(num1, num2);
}

// Converters
int s21_from_int_to_decimal(int src, s21_decimal* dst) {
    int res = CONVERTING_ERROR;
    if (dst) {
        dec_init(dst);
        if (src < 0) {
            dst->bits[S] = SIGNMASK;
        }
        dst->bits[L] = abs(src);
        res = SUCCESS;
    }
    return res;
}

int s21_from_int64_to_decimal(int64_t src, s21_decimal* dst) {
    int res = CONVERTING_ERROR;
    if (dst) {
        dec_init(dst);
        if (src < 0) {
            dst->bits[S] = SIGNMASK;
            src = ~(src) + 1;
        }
        dst->bits[L] = (unsigned int)src;
        dst->bits[M] = (unsigned int)(src >> 32);
        res = SUCCESS;
    }
    return res;
}

int s21_from_float_to_decimal(float src, s21_decimal* dst) {
    int res = CONVERTING_ERROR;
    if (dst) {
        dec_init(dst);
        fs orig;
        orig.fl = src;
        bool sign = orig.dw >> 31;
        if (isinf(src) && !sign) {
            dst->value_type = S21_INFINITY;
        } else if (isinf(src) && sign) {
            dst->value_type = S21_NEGATIVE_INFINITY;
        } else if (isnan(src)) {
            dst->value_type = S21_NAN;
        } else if (src == 0.0) {
            res = SUCCESS;
        } else {
            // https://en.wikipedia.org/wiki/Single-precision_floating-point_format
            // https://habr.com/ru/post/112953/
            int scale = 0;
            int exp = ((orig.dw & ~SIGNMASK) >> 23) - 127;
            double tmp = fabs(src);
            while (scale <= MAXSCALE &&
                   ((int32_t)tmp / 2097152) == 0) {  // 2097152 = 2^21
                tmp *= 10;
                scale++;
            }
            tmp = round(tmp);
            if (scale <= MAXSCALE && (exp > -94 && exp < 96)) {
                fs m;
                tmp = (float)tmp;
                while (fmod(tmp, 10) == 0 && scale > 0) {
                    tmp /= 10;
                    scale--;
                }
                m.fl = tmp;
                exp = ((m.dw & ~SIGNMASK) >> 23) - 127;
                set_bit(dst, exp);
                for (int i = exp - 1, j = 22; j >= 0; i--, j--) {
                    if ((m.dw & (1 << j)) != 0) {
                        set_bit(dst, i);
                    }
                }
                set_scale(dst, scale);
                set_sign(dst, sign);
                res = TRUE;
            }
        }
    }
    return res;
}

int s21_from_decimal_to_int(s21_decimal src, int* dst) {
    int res = CONVERTING_ERROR;
    if (dst) {
        if (s21_is_normal(src)) {
            if (get_scale(src) > 0) {
                src = s21_truncate(src);
            }
            if (src.bits[H] == 0 && src.bits[M] == 0) {
                *dst = src.bits[L];
                if (get_sign(src) == 1) {
                    *dst = ~(*dst) + 1;
                }
                res = SUCCESS;
            }
        }
    }
    return res;
}

int s21_from_decimal_to_int64(s21_decimal src, int64_t* dst) {
    int res = CONVERTING_ERROR;
    if (dst) {
        if (s21_is_normal(src)) {
            if (get_scale(src)) {
                src = s21_truncate(src);
            }
            if (src.bits[H] == 0) {
                *dst = (src.bits[L] & 0xFFFFFFFFL) | ((int64_t)src.bits[M] << 32);
                if (get_sign(src) == 1) {
                    *dst = ~(*dst) + 1;
                }
                res = SUCCESS;
            }
        }
    }
    return res;
}

// Конвертация decimal во float, в соответствии с C#
// Но нужно ли??
int s21_from_decimal_to_float(s21_decimal src, float* dst) {
    int res = CONVERTING_ERROR;
    if (s21_is_normal(src) && dst) {
        double tmp = 0;
        for (int i = 0; i < 96; i++) {
            if (get_bit(src, i)) {
                tmp += pow(2, i);
            }
        }
        int scale = get_scale(src);
        if (scale > 0) {
            tmp *= pow(10, -scale);
        }
        *dst = (float)tmp;
        if (get_sign(src) == 1) {  // negative number
            *dst *= -1;
        }
        res = TRUE;
    }
    return res;
}

// Other features
s21_decimal s21_floor(s21_decimal src) {
    s21_decimal res = DEC_ZERO;
    if (s21_is_inf(src) || s21_is_nan(src)) {
        res.value_type = src.value_type;
    } else if (s21_is_zero(src) == 0) {  // not zero
        res = s21_truncate(src);
        if (get_sign(src) == 1 && get_scale(src) > 0) {
            s21_decimal minus_one = DEC_MINUS_ONE;
            res = s21_add(res, minus_one);
        }
    }
    return res;
}

s21_decimal s21_round(s21_decimal src) {
    s21_decimal res = DEC_ZERO;
    if (s21_is_inf(src) || s21_is_nan(src)) {
        res.value_type = src.value_type;
    } else if (s21_is_zero(src) == 0) {  // not zero
        if (get_scale(src) > 0) {
            bool sign = get_sign(src);  // save sign
            src = s21_abs(src);

            res = s21_truncate(src);
            s21_decimal remainder;
            if (s21_is_zero(res)) {
                remainder = src;
            } else {
                remainder = s21_sub(src, res);
            }
            s21_decimal half = {{5, 0, 0, 0x00010000}, S21_NORMAL_VALUE};  // 0.5
            s21_normalize(&remainder,
                          &half);  // Adjustment of control number to remainder
            // Rounding
            if (s21_is_greater_or_equal(remainder, half) == TRUE) {  // >=
                s21_decimal one = DEC_ONE;
                res = s21_add(res, one);
            }

            if (sign == 1) {  // restore sign
                res = s21_negate(res);
            }
        } else {
            res = src;
        }
    }
    return res;
}

s21_decimal s21_truncate(s21_decimal src) {
    s21_decimal res = DEC_ZERO;
    if (s21_is_inf(src) || s21_is_nan(src)) {
        res.value_type = src.value_type;
    } else if (s21_is_zero(src) == 0) {  // not zero
        int scale = get_scale(src);
        if (scale > 0) {
            do {
                int pow10Idx = (scale > MAXINTSCALE) ? MAXINTSCALE : scale;
                s21_div_by_int32(&src, pow10Array[pow10Idx]);
                scale -= pow10Idx;
            } while (scale > 0);  // Decrease the exponent until it becomes 0
            set_scale(&src, scale);
        }
        res = src;
    }
    return res;
}

s21_decimal s21_negate(s21_decimal src) {
    if (src.value_type == S21_INFINITY) {
        src.value_type = S21_NEGATIVE_INFINITY;
    } else if (src.value_type == S21_NEGATIVE_INFINITY) {
        src.value_type = S21_INFINITY;
    } else {
        if (s21_is_zero(src) == 0) {  // not zero
            set_sign(&src, !get_sign(src));
        }
    }
    return src;
}

s21_decimal s21_abs(s21_decimal src) {
    if (s21_is_normal(src)) {
        set_sign(&src, 0);
    } else if (src.value_type == S21_NEGATIVE_INFINITY) {
        src.value_type = S21_INFINITY;
    }
    return src;
}
