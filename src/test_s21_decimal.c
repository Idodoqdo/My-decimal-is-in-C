#include "test_s21_decimal.h"

START_TEST(s21_addition_random_test) {
  int i, num1, num2;
  s21_decimal number1, number2, res1, res2;

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(5000), num2 = random_int(3400);
    valToLog("s21_add", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_add, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_add, num 2", number2);
    res1 = s21_add(number1, number2);
    decToLog("function: s21_add, res 1", res1);
    s21_from_int_to_decimal(num1 + num2, &res2);
    decToLog("function: s21_add, res 2", res2);
    ck_assert_int_eq(dec_eq(res1, res2), 1);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(5000), num2 = random_int(3000) * -1;
    valToLog("s21_add", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_add, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_add, num 2", number2);
    res1 = s21_add(number1, number2);
    decToLog("function: s21_add, res 1", res1);
    s21_from_int_to_decimal(num1 + num2, &res2);
    decToLog("function: s21_add, res 2", res2);
    ck_assert_int_eq(dec_eq(res1, res2), 1);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i < TDA_SIZE; i++) {
    number1 = tda_num1[i];
    number2 = tda_num2[i];
    decToLog("function: s21_add, num 1", number1);
    decToLog("function: s21_add, num 2", number2);
    res1 = s21_add(number1, number2);
    decToLog("function: s21_add, res 1", res1);
    decToLog("function: s21_add, res 2", tda_res_add[i]);
    ck_assert_int_eq(dec_eq(res1, tda_res_add[i]), 1);
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_addition_1) {
  s21_decimal src1, src2;
  int a = -1234;
  float b = 1.234;
  float res_our_dec = 0.0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -1232.766;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_2) {
  s21_decimal src1, src2;
  int a = -1234;
  float b = -1.234;
  float res_our_dec = 0.0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -1235.234;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_3) {
  s21_decimal src1, src2;
  int a = -46;
  float b = NAN;
  float res_our_dec = 0.0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_addition_4) {
  s21_decimal src1, src2;
  float a = -1234;
  float b = -221.234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -1455.234;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_5) {
  s21_decimal src1, src2;
  int a = -1234;
  float b = -221.234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -1455.234;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_6) {
  s21_decimal src1, src2;
  float a = -INFINITY;
  int b = 202;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NEGATIVE_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_addition_7) {
  s21_decimal src1, src2;
  float a = -9403;
  float b = 0.00234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -9402.99766;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_8) {
  s21_decimal src1, src2;
  int a = -9403;
  int b = 234;
  int res_our_dec = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  int res_origin = -9169;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_int(res_od, &res_our_dec);
  ck_assert_int_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_9) {
  s21_decimal src1, src2;
  float a = -940.3;
  float b = 0.000234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -940.299766;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_10) {
  s21_decimal src1, src2;
  float a = -0.9403;
  float b = 0.000234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -0.940066;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_11) {
  s21_decimal src1, src2;
  float a = -0.9403;
  float b = 2.0234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = 1.0831;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_12) {
  s21_decimal src1, src2;
  float a = INFINITY;
  float b = 112.0234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od;
  res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_addition_13) {
  s21_decimal src1, src2;
  float a = -0.9403;
  float b = -112.0234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -112.9637;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_14) {
  s21_decimal src1, src2;
  float a = -0.94e03;
  float b = -112.0234;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -1052.0234;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_15) {
  s21_decimal src1, src2;
  float a = -0.94e03;
  float b = -112.0e2;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -12140;
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_16) {
  s21_decimal src1, src2;
  int a = 9403;
  int b = 202;
  int res_origin = 9605;
  int res_our_dec = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  s21_decimal res_od = s21_add(src1, src2);
  s21_from_decimal_to_int(res_od, &res_our_dec);
  ck_assert_int_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_addition_17) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.value_type = src2.value_type = S21_NORMAL_VALUE;
  src1.bits[3] = 0x300000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xF;
  src1.bits[0] = 0x67E4FEEF;
  src2.bits[3] = 0x300000;
  src2.bits[2] = 0;
  src2.bits[1] = 0xFF;
  src2.bits[0] = 0x67E4FFFF;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x10E;
  result_origin.bits[0] = 0xCFC9FEEE;
  s21_decimal result_our = s21_add(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_addition_18) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0x30000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xFF;
  src1.bits[0] = 0x67E4F;
  src2.bits[3] = 0x60000;
  src2.bits[2] = 0;
  src2.bits[1] = 0xEA;
  src2.bits[0] = 0x67E4F;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0x60000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x3E502;
  result_origin.bits[0] = 0x1963E2E7;
  s21_decimal result_our = s21_add(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_addition_19) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0x30000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xFFFF;
  src1.bits[0] = 0xFF837E4F;
  src2.bits[3] = 0x80070000;
  src2.bits[2] = 0;
  src2.bits[1] = 0xFFF;
  src2.bits[0] = 0xFF837E4F;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0x70000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x270FEFED;
  result_origin.bits[0] = 0x00F26FA1;
  s21_decimal result_our = s21_add(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_addition_20) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0x80030000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xFFFF;
  src1.bits[0] = 0xFF837E4F;
  src2.bits[3] = 0x80070000;
  src2.bits[2] = 0;
  src2.bits[1] = 0xFFF;
  src2.bits[0] = 0xFF837E4F;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0x80070000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x27100FEC;
  result_origin.bits[0] = 0xFFF96C3F;
  s21_decimal result_our = s21_add(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_addition_21) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0x80030000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xFFFF;
  src1.bits[0] = 0xFF837E4F;
  src2.bits[3] = 0x70000;
  src2.bits[2] = 0;
  src2.bits[1] = 0xFFF;
  src2.bits[0] = 0xFF837E4F;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0x80070000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x270FEFED;
  result_origin.bits[0] = 0x00F26FA1;
  s21_decimal result_our = s21_add(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_addition_22) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO, result_our;
  float inf = INFINITY;
  float neg_inf = -INFINITY;
  float number = -random_float();
  float zero = 0.0;
  s21_from_float_to_decimal(inf, &src1);
  s21_from_float_to_decimal(neg_inf, &src2);
  result_our = s21_add(src1, src2);
  ck_assert_int_eq(S21_NAN, result_our.value_type);

  s21_from_float_to_decimal(number, &src1);
  s21_from_float_to_decimal(inf, &src2);
  result_our = s21_add(src1, src2);
  ck_assert_int_eq(src2.value_type, result_our.value_type);

  s21_from_float_to_decimal(number, &src1);
  s21_from_float_to_decimal(zero, &src2);
  result_our = s21_add(src1, src2);
  ck_assert_int_eq(dec_eq(src1, result_our), 1);
}
END_TEST

START_TEST(s21_substraction_random_test) {
  int i, num1, num2;
  s21_decimal number1, number2, res1, res2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(5000), num2 = random_int(5500);
    valToLog("s21_sub", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_sub, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_sub, num 2", number2);
    res1 = s21_sub(number1, number2);
    decToLog("function: s21_sub, res 1", res1);
    s21_from_int_to_decimal(num1 - num2, &res2);
    decToLog("function: s21_sub, res 2", res2);
    writeLog("------------");
    ck_assert_int_eq(dec_eq(res1, res2), 1);
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(5000), num2 = random_int(100) * -1;
    valToLog("s21_sub", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_sub, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_sub, num 2", number2);
    res1 = s21_sub(number1, number2);
    decToLog("function: s21_sub, res 1", res1);
    s21_from_int_to_decimal(num1 - num2, &res2);
    decToLog("function: s21_sub, res 2", res2);
    writeLog("------------");
    ck_assert_int_eq(dec_eq(res1, res2), 1);
  }
  writeLog("----- next -----");

  for (i = 0; i < TDA_SIZE; i++) {
    number1 = tda_num1[i];
    number2 = tda_num2[i];
    decToLog("function: s21_sub, num 1", number1);
    decToLog("function: s21_sub, num 2", number2);
    res1 = s21_sub(number1, number2);
    decToLog("function: s21_sub, res 1", res1);
    decToLog("function: s21_sub, res 2", tda_res_sub[i]);
    ck_assert_int_eq(dec_eq(res1, tda_res_sub[i]), 1);
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_substraction_1) {
  s21_decimal src1, src2;
  int a = 9403;
  int b = 202;
  int res_our_dec = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  int res_origin = 9201;
  s21_decimal res_od = s21_sub(src1, src2);
  s21_from_decimal_to_int(res_od, &res_our_dec);
  ck_assert_int_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_substraction_2) {
  s21_decimal src1, src2;
  int a = 9403;
  float b = 202.098;
  float res_our_dec = 0.0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = 9200.902;
  s21_decimal res_od = s21_sub(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_substraction_3) {
  s21_decimal src1, src2;
  float a = -9403;
  float b = 202.098;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = a - b;
  s21_decimal res_od = s21_sub(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_substraction_4) {
  s21_decimal src1, src2;
  float a = 9403.0;
  float b = 202.09e8;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -20208990597;
  s21_decimal res_od = s21_sub(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_substraction_5) {
  s21_decimal src1, src2;
  float a = 9403.0e2;
  float b = 202.09e8;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -20208059700;
  s21_decimal res_od = s21_sub(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_substraction_6) {
  s21_decimal src1, src2;
  float a = -9403.0e2;
  int b = -202;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  float res_origin = a - b;
  s21_decimal res_od = s21_sub(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_substraction_7) {
  s21_decimal src1, src2;
  float a = -INFINITY;
  int b = 202;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  s21_decimal res_od = s21_sub(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NEGATIVE_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_substraction_8) {
  s21_decimal src1, src2;
  float a = -94;
  float b = -202;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = a - b;
  s21_decimal res_od = s21_sub(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_substraction_9) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0b00000000000000010000000000000000;
  src1.bits[2] = 0;
  src1.bits[1] = 0;
  src1.bits[0] = 0b00000000000000000110011011110000;
  src2.bits[3] = 0b00000000000000110000000000000000;
  src2.bits[2] = 0;
  src2.bits[1] = 0;
  src2.bits[0] = 0b00000000000001000101000111010110;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0b00000000000000110000000000000000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0;
  result_origin.bits[0] = 0b00000000001000111110001111101010;
  s21_decimal result_our = s21_sub(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_substraction_10) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0b00000000000000110000000000000000;
  src1.bits[2] = 0;
  src1.bits[1] = 0;
  src1.bits[0] = 0b00000000000001000101000111010110;
  src2.bits[3] = 0b00000000000000010000000000000000;
  src2.bits[2] = 0;
  src2.bits[1] = 0;
  src2.bits[0] = 0b00000000000000000000101110111100;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0b10000000000000110000000000000000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0;
  result_origin.bits[0] = 0b00000000000000000100001110011010;
  s21_decimal result_our = s21_sub(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_substraction_11) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0x80030000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xFFFF;
  src1.bits[0] = 0xFF837E4F;
  src2.bits[3] = 0x80070000;
  src2.bits[2] = 0;
  src2.bits[1] = 0xFFF;
  src2.bits[0] = 0xFF837E4F;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0x80070000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x270FEFED;
  result_origin.bits[0] = 0x00F26FA1;
  s21_decimal result_our = s21_sub(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_substraction_12) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0x30000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xFFFF;
  src1.bits[0] = 0xFF837E4F;
  src2.bits[3] = 0x80070000;
  src2.bits[2] = 0;
  src2.bits[1] = 0xFFF;
  src2.bits[0] = 0xFF837E4F;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0x70000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x27100FEC;
  result_origin.bits[0] = 0xFFF96C3F;
  s21_decimal result_our = s21_sub(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_substraction_13) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0b10000000000000010000000000000000;
  src1.bits[2] = 0;
  src1.bits[1] = 0;
  src1.bits[0] = 0b00000000000000000000000100110000;
  src2.bits[3] = 0b10000000000001100000000000000000;
  src2.bits[2] = 0;
  src2.bits[1] = 0;
  src2.bits[0] = 0b00010001001000010001101001100000;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0b00000000000001100000000000000000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0;
  result_origin.bits[0] = 0b00001111010100010011110001100000;
  s21_decimal result_our = s21_sub(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_substraction_14) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[3] = 0x80030000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xFFFF;
  src1.bits[0] = 0xFF837E4F;
  src2.bits[3] = 0x70000;
  src2.bits[2] = 0;
  src2.bits[1] = 0xFFF;
  src2.bits[0] = 0xFF837E4F;
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0x80070000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x27100FEC;
  result_origin.bits[0] = 0xFFF96C3F;
  s21_decimal result_our = s21_sub(src1, src2);
  ck_assert_int_eq(result_origin.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_substraction_15) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO;
  src1.bits[0] = 0b00000000000000000000011111100100;
  src1.bits[1] = 0b00000000000000000000000000000000;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000000000000000000000000;
  src2.bits[0] = 0b00000101100110111101101000011001;
  src2.bits[1] = 0b00000000000000000000000000000000;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal result = DEC_ZERO, result_our;
  result_our = s21_sub(src2, src1);
  result.bits[0] = 0b00000101100110111101001000110101;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b00000000000000000000000000000000;
  ck_assert_int_eq(result.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_substraction_16) {
  s21_decimal src1, src2;
  src1.value_type = src2.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00000000000000000000011111100100;
  src1.bits[1] = 0b00000000000000000000000000000000;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b10000000000000000000000000000000;
  src2.bits[0] = 0b00000000000000000010010010111011;
  src2.bits[1] = 0b00000000000000000000000000000000;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b10000000000000000000000000000000;
  s21_decimal result = DEC_ZERO, result_our;
  result_our = s21_sub(src2, src1);
  result.bits[0] = 0b00000000000000000001110011010111;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b10000000000000000000000000000000;
  ck_assert_int_eq(result.bits[3], result_our.bits[3]);
  ck_assert_int_eq(result.bits[2], result_our.bits[2]);
  ck_assert_int_eq(result.bits[1], result_our.bits[1]);
  ck_assert_int_eq(result.bits[0], result_our.bits[0]);
}
END_TEST

START_TEST(s21_substraction_17) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO, result_our;
  float inf = INFINITY;
  float neg_inf = -INFINITY;
  float nan = NAN;
  float number = -random_float();
  float zero = 0.0;

  s21_from_float_to_decimal(inf, &src1);
  s21_from_float_to_decimal(neg_inf, &src2);
  result_our = s21_sub(src1, src2);
  ck_assert_int_eq(src1.value_type, result_our.value_type);

  s21_from_float_to_decimal(inf, &src2);
  result_our = s21_sub(src1, src2);
  ck_assert_int_eq(S21_NAN, result_our.value_type);

  s21_from_float_to_decimal(number, &src1);
  result_our = s21_sub(src1, src2);
  src2 = s21_negate(src2);
  ck_assert_int_eq(src2.value_type, result_our.value_type);

  s21_from_float_to_decimal(zero, &src1);
  s21_from_float_to_decimal(nan, &src2);
  result_our = s21_sub(src1, src2);
  ck_assert_int_eq(S21_NAN, result_our.value_type);

  s21_from_float_to_decimal(zero, &src1);
  s21_from_float_to_decimal(number, &src2);
  result_our = s21_sub(src1, src2);
  src2 = s21_negate(src2);
  ck_assert_int_eq(dec_eq(src2, result_our), 1);

  s21_from_float_to_decimal(number, &src1);
  s21_from_float_to_decimal(zero, &src2);
  result_our = s21_sub(src1, src2);
  ck_assert_int_eq(dec_eq(src1, result_our), 1);
}
END_TEST

START_TEST(s21_multiply_random_test) {
  int i;
  int64_t num1, num2;
  s21_decimal number1, number2, res1, res2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(10000), num2 = random_int(5000);
    valToLog("s21_mul", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_mul, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_mul, num 2", number2);
    res1 = s21_mul(number1, number2);
    decToLog("function: s21_mul, res 1", res1);
    s21_from_int_to_decimal(num1 * num2, &res2);
    decToLog("function: s21_mul, res 2", res2);
    writeLog("------------");
    ck_assert_int_eq(dec_eq(res1, res2), 1);
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(2000), num2 = random_int(1000) * -1;
    valToLog("s21_mul", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_mul, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_mul, num 2", number2);
    res1 = s21_mul(number1, number2);
    decToLog("function: s21_mul, res 1", res1);
    s21_from_int_to_decimal(num1 * num2, &res2);
    decToLog("function: s21_mul, res 2", res2);
    writeLog("------------");
    ck_assert_int_eq(dec_eq(res1, res2), 1);
  }
  writeLog("----- next -----");

  for (i = 0; i < TDA_SIZE; i++) {
    number1 = tda_num1[i];
    number2 = tda_num2[i];
    decToLog("function: s21_mul, num 1", number1);
    decToLog("function: s21_mul, num 2", number2);
    res1 = s21_mul(number1, number2);
    decToLog("function: s21_mul, res 1", res1);
    decToLog("function: s21_mul, res 2", tda_res_mul[i]);
    ck_assert_int_eq(dec_eq(res1, tda_res_mul[i]), 1);
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_multiply_1) {
  s21_decimal src1, src2;
  float a = 9403.0e2;
  int b = 202;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  float res_origin = 189940600;
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_multiply_2) {
  s21_decimal src1, src2;
  float a = 9403.0e2;
  float b = 9403.0e2;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = 884164090000;
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_multiply_3) {
  s21_decimal src1, src2;
  int a = 9403;
  int b = 202;
  int res_our_dec = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  int res_origin = 1899406;
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_int(res_od, &res_our_dec);
  ck_assert_int_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_multiply_4) {
  s21_decimal src1, src2;
  int a = -32768;
  int b = 2;
  int res_our_dec = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  int res_origin = -65536;
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_int(res_od, &res_our_dec);
  ck_assert_int_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_multiply_5) {
  s21_decimal src1, src2;
  int a = -32768;
  int b = 32768;
  int res_our_dec = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  int res_origin = -1073741824;
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_int(res_od, &res_our_dec);
  ck_assert_int_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_multiply_6) {
  s21_decimal src1, src2;
  float a = INFINITY;
  int b = 0;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_7) {
  s21_decimal src1, src2;
  float a = INFINITY;
  float b = 132;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_8) {
  s21_decimal src1, src2;
  float a = INFINITY;
  float b = INFINITY;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_9) {
  s21_decimal src1, src2;
  float a = INFINITY;
  float b = NAN;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_10) {
  s21_decimal src1, src2;
  float a = INFINITY;
  float b = -INFINITY;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_11) {
  s21_decimal src1, src2;
  float a = -INFINITY;
  float b = 123;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NEGATIVE_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_12) {
  s21_decimal src1, src2;
  float a = -INFINITY;
  float b = -123;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_13) {
  s21_decimal src1, src2;
  float a = INFINITY;
  float b = 132;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src2, src1);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_14) {
  s21_decimal src1, src2;
  float a = -INFINITY;
  float b = 123;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src2, src1);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NEGATIVE_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_15) {
  s21_decimal src1, src2;
  float a = INFINITY;
  int b = 0;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src2, src1);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_16) {
  s21_decimal src1, src2;
  float a = -INFINITY;
  float b = NAN;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src2, src1);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_17) {
  s21_decimal src1, src2;
  float a = -INFINITY;
  float b = NAN;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_18) {
  s21_decimal src1, src2;
  float a = NAN;
  float b = NAN;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_mul(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_multiply_19) {
  s21_decimal src1, src2, res_od;
  int64_t a = random_int(INT32_MAX) + random_int(INT32_MAX);
  int b = 1;
  s21_from_int64_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_od = s21_mul(src1, src2);
  ck_assert_int_eq(dec_eq(src1, res_od), 1);

  src2 = s21_negate(src2);
  res_od = s21_mul(src1, src2);
  src1 = s21_negate(src1);
  ck_assert_int_eq(dec_eq(src1, res_od), 1);
}
END_TEST

START_TEST(s21_multiply_20) {
  s21_decimal src1, src2, res_control, res_od;
  int64_t a = random_int(INT32_MAX);
  int64_t b = random_int(10000);
  int64_t res = a * b;
  s21_from_int64_to_decimal(a, &src1);
  s21_from_int64_to_decimal(b, &src2);
  s21_from_int64_to_decimal(res, &res_control);
  res_od = s21_mul(src1, src2);
  ck_assert_int_eq(dec_eq(res_control, res_od), 1);

  res_od = s21_negate(res_od);
  int64_t res_int;
  s21_from_decimal_to_int64(res_od, &res_int);
  ck_assert_int_eq(res_int, -res);
}
END_TEST

START_TEST(s21_multiply_21) {
  s21_decimal src1, src2, origin;
  // src1 = 79228162514264337593543950335;
  // src2 = 79228162514264337593543950335;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11111111111111111111111111111111;
  src1.bits[1] = 0b11111111111111111111111111111111;
  src1.bits[2] = 0b11111111111111111111111111111111;
  src1.bits[3] = 0b00000000000000000000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b11111111111111111111111111111111;
  src2.bits[1] = 0b11111111111111111111111111111111;
  src2.bits[2] = 0b11111111111111111111111111111111;
  src2.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal result = s21_mul(src1, src2);
  origin.value_type = S21_INFINITY;
  origin.bits[0] = 0b00000000000000000000000000000000;
  origin.bits[1] = 0b00000000000000000000000000000000;
  origin.bits[2] = 0b00000000000000000000000000000000;
  origin.bits[3] = 0b00000000000000000000000000000000;
  ck_assert_int_eq(origin.bits[3], result.bits[3]);
  ck_assert_int_eq(origin.bits[2], result.bits[2]);
  ck_assert_int_eq(origin.bits[1], result.bits[1]);
  ck_assert_int_eq(origin.bits[0], result.bits[0]);
  ck_assert_int_eq(origin.value_type, result.value_type);
}
END_TEST

START_TEST(s21_multiply_22) {
  s21_decimal src1, src2, origin;
  // src1 = 9999999999999999999;
  // src2 = 1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b10001001111001111111111111111111;
  src1.bits[1] = 0b10001010110001110010001100000100;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000000000000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b00000000000000000000000000000001;
  src2.bits[1] = 0b00000000000000000000000000000000;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal result = s21_mul(src1, src2);
  origin.value_type = S21_NORMAL_VALUE;
  origin.bits[0] = 0b10001001111001111111111111111111;
  origin.bits[1] = 0b10001010110001110010001100000100;
  origin.bits[2] = 0b00000000000000000000000000000000;
  origin.bits[3] = 0b00000000000000000000000000000000;
  ck_assert_int_eq(origin.bits[3], result.bits[3]);
  ck_assert_int_eq(origin.bits[2], result.bits[2]);
  ck_assert_int_eq(origin.bits[1], result.bits[1]);
  ck_assert_int_eq(origin.bits[0], result.bits[0]);
  ck_assert_int_eq(origin.value_type, result.value_type);
}
END_TEST

START_TEST(s21_multiply_23) {
  s21_decimal src1, src2, origin;
  // src1 = 0.0;
  // src2 = 3;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00000000000000000000000000000000;
  src1.bits[1] = 0b00000000000000000000000000000000;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000000010000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b00000000000000000000000000000011;
  src2.bits[1] = 0b00000000000000000000000000000000;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal result = s21_mul(src1, src2);
  origin.value_type = S21_NORMAL_VALUE;
  origin.bits[0] = 0b00000000000000000000000000000000;
  origin.bits[1] = 0b00000000000000000000000000000000;
  origin.bits[2] = 0b00000000000000000000000000000000;
  origin.bits[3] = 0b00000000000000010000000000000000;
  ck_assert_int_eq(origin.bits[3], result.bits[3]);
  ck_assert_int_eq(origin.bits[2], result.bits[2]);
  ck_assert_int_eq(origin.bits[1], result.bits[1]);
  ck_assert_int_eq(origin.bits[0], result.bits[0]);
  ck_assert_int_eq(origin.value_type, result.value_type);
}
END_TEST

START_TEST(s21_division_random_test) {
  int i, num1, num2;
  s21_decimal number1, number2, res1, res2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000), num2 = devider(num1);
    valToLog("s21_div", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_div, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_div, num 2", number2);
    res1 = s21_div(number1, number2);
    decToLog("function: s21_div, res 1", res1);
    s21_from_int_to_decimal(num1 / num2, &res2);
    decToLog("function: s21_div, res 2", res2);
    writeLog("------------");
    ck_assert_int_eq(dec_eq(res1, res2), 1);
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(100000), num2 = devider(num1) * -1;
    valToLog("s21_div", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_div, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_div, num 2", number2);
    res1 = s21_div(number1, number2);
    decToLog("function: s21_div, res 1", res1);
    s21_from_int_to_decimal(num1 / num2, &res2);
    decToLog("function: s21_div, res 2", res2);
    writeLog("------------");
    ck_assert_int_eq(dec_eq(res1, res2), 1);
  }
  writeLog("----- next -----");

  for (i = 0; i < TDA_SIZE; i++) {
    number1 = tda_num1[i];
    number2 = tda_num2[i];
    decToLog("function: s21_div, num 1", number1);
    decToLog("function: s21_div, num 2", number2);
    res1 = s21_div(number1, number2);
    decToLog("function: s21_div, res 1", res1);
    decToLog("function: s21_div, res 2", tda_res_div[i]);
    ck_assert_int_eq(dec_eq(res1, tda_res_div[i]), 1);
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_division_1) {
  s21_decimal src1, src2;
  float a = 9403.0e2;
  int b = 202;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  float res_origin = 4654.950495049504950495049505;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_2) {
  s21_decimal src1, src2;
  int a = -32768;
  int b = 2;
  int res_our_dec = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  int res_origin = -16384;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_int(res_od, &res_our_dec);
  ck_assert_int_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_3) {
  s21_decimal src1, src2;
  float a = -9403.0e2;
  float b = -2020.29;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = 465.4282306005573457275935633;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_4) {
  s21_decimal src1, src2;
  float a = -9403.0e2;
  float b = 2020.29;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = -465.4282306005573457275935633;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_5) {
  s21_decimal src1, src2;
  float a = -9403.0e20;
  float b = 2.28e17;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = a / b;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_6) {
  s21_decimal src1, src2;
  float a = -0.9;
  float b = 30.323;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = a / b;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_7) {
  s21_decimal src1, src2;
  float a = -0.9e3;
  float b = 30.32;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = a / b;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_8) {
  s21_decimal src1, src2;
  float a = -0.9e3;
  int b = 30;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  float res_origin = a / b;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_9) {
  s21_decimal src1, src2;
  float a = -0.9;
  float b = 0.000076;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  float res_origin = a / b;
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_our_dec, res_origin);
}
END_TEST

START_TEST(s21_division_10) {
  s21_decimal src1 = DEC_ZERO, src2 = DEC_ZERO, src3;
  src3.value_type = S21_NAN;
  s21_decimal res_od = s21_div(src1, src2);
  ck_assert_int_eq(res_od.value_type, src3.value_type);
}
END_TEST

START_TEST(s21_division_11) {
  s21_decimal src1, src2, src3;
  s21_from_int_to_decimal(10, &src1);
  s21_from_int_to_decimal(0, &src2);
  src3.value_type = S21_INFINITY;
  s21_decimal res_od = s21_div(src1, src2);

  ck_assert_int_eq(res_od.value_type, src3.value_type);
}
END_TEST

START_TEST(s21_division_12) {
  s21_decimal src1, src2;
  s21_from_int_to_decimal(-10, &src1);
  src1.value_type = S21_NORMAL_VALUE;
  src2.value_type = S21_NEGATIVE_INFINITY;
  s21_decimal res_od = s21_div(src1, src2);
  ck_assert_int_eq(res_od.value_type, S21_NORMAL_VALUE);
}
END_TEST

START_TEST(s21_division_13) {
  s21_decimal src1, src2;
  float a = INFINITY;
  float b = INFINITY;
  float res_our_dec = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_div(src1, src2);
  s21_from_decimal_to_float(res_od, &res_our_dec);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_division_14) {
  s21_decimal src1, src2;
  src1.value_type = src2.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b01110001001110010011101000100111;
  src1.bits[1] = 0b00000000000000000000000011100010;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000001010000000000000000;
  src2.bits[0] = 0b00000000000000010111101111011011;
  src2.bits[1] = 0b00000000000000000000000000000000;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b00000000000000100000000000000000;
  s21_decimal result_origin;
  result_origin.value_type = S21_NORMAL_VALUE;
  result_origin.bits[0] = 0b00100000111100011100110110110001;
  result_origin.bits[1] = 0b01011000000100101111110011101001;
  result_origin.bits[2] = 0b00100000010100001110111000110111;
  result_origin.bits[3] = 0b00000000000110000000000000000000;
  s21_decimal res_od = s21_div(src1, src2);
  float a, b;
  s21_from_decimal_to_float(result_origin, &a);
  s21_from_decimal_to_float(res_od, &b);
  ck_assert_float_eq(a, b);
}
END_TEST

START_TEST(s21_division_15) {
  s21_decimal src1, src2;
  src1.value_type = src2.value_type = S21_NORMAL_VALUE;
  // 7643756234.84743
  src1.bits[0] = 0b00010001100000110100010101000111;
  src1.bits[1] = 0b00000000000000101011011100110010;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000001010000000000000000;
  // 934562237.12843
  src2.bits[0] = 0b01111001000001000011011001001011;
  src2.bits[1] = 0b00000000000000000101010011111111;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b00000000000001010000000000000000;
  s21_decimal result_origin;
  // 8.178969715632758783748379499
  result_origin.value_type = S21_NORMAL_VALUE;
  result_origin.bits[0] = 0b01000111110000001001001101101011;
  result_origin.bits[1] = 0b10111000000101111000101110100000;
  result_origin.bits[2] = 0b00011010011011010111110000110100;
  result_origin.bits[3] = 0b00000000000110110000000000000000;
  s21_decimal res_od = s21_div(src1, src2);
  float a, b;
  s21_from_decimal_to_float(result_origin, &a);
  s21_from_decimal_to_float(res_od, &b);
  ck_assert_float_eq(a, b);
}
END_TEST

START_TEST(s21_division_16) {
  s21_decimal src1, src2;
  int a = -17272;
  float b = -INFINITY;
  s21_from_int_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_div(src1, src2);
  ck_assert_int_eq(res_od.value_type, S21_NORMAL_VALUE);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_division_17) {
  s21_decimal src1, src2, src3;
  src1.value_type = S21_NORMAL_VALUE;
  src2.value_type = S21_NAN;
  src3.value_type = S21_NAN;
  s21_decimal res_od = s21_div(src1, src2);
  ck_assert_int_eq(res_od.value_type, src3.value_type);
}
END_TEST

START_TEST(s21_division_18) {
  s21_decimal src1, src2;
  float a = -115.2;
  float b = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  s21_decimal res_od = s21_div(src1, src2);

  ck_assert_int_eq(res_od.value_type, S21_NEGATIVE_INFINITY);
  ck_assert_int_eq(res_od.bits[3], 0);
  ck_assert_int_eq(res_od.bits[2], 0);
  ck_assert_int_eq(res_od.bits[1], 0);
  ck_assert_int_eq(res_od.bits[0], 0);
}
END_TEST

START_TEST(s21_division_19) {
  s21_decimal src1, src2, res_od;
  int64_t a = random_int(INT32_MAX) + random_int(INT32_MAX);
  int b = 1;
  float inf = INFINITY;
  float neg_inf = -INFINITY;

  s21_from_int64_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_od = s21_div(src1, src2);
  ck_assert_int_eq(dec_eq(src1, res_od), 1);

  src2 = s21_negate(src2);  // -1
  res_od = s21_div(src1, src2);
  src1 = s21_negate(src1);
  ck_assert_int_eq(dec_eq(src1, res_od), 1);

  s21_from_float_to_decimal(inf, &src1);
  res_od = s21_div(src1, src2);
  ck_assert_int_eq(S21_NEGATIVE_INFINITY, res_od.value_type);

  s21_from_float_to_decimal(neg_inf, &src1);
  res_od = s21_div(src1, src2);
  ck_assert_int_eq(S21_INFINITY, res_od.value_type);
}
END_TEST

START_TEST(s21_division_20) {
  s21_decimal src1 = DEC_ZERO, src2, res_od;
  int64_t b = random_int(INT32_MAX) + random_int(INT32_MAX);
  int res;

  int scale1 = random_int(28), scale2 = random_int(28);
  s21_from_int64_to_decimal(b, &src2);
  src1.bits[S] = scale1 << SCALESHIFT;
  src2.bits[S] = scale2 << SCALESHIFT;
  res_od = s21_div(src1, src2);
  s21_from_decimal_to_int(res_od, &res);
  ck_assert_int_eq(res, 0);
  int res_scale = (res_od.bits[S] & SCALEMASK) >> SCALESHIFT;
  int scale = (scale1 < scale2) ? 0 : scale1 - scale2;
  ck_assert_int_eq(res_scale, scale);

  b = random_int(INT32_MAX) + random_int(INT32_MAX);
  s21_from_int64_to_decimal(b, &src2);
  src1 = src2;
  res_od = s21_div(src1, src2);
  s21_from_decimal_to_int(res_od, &res);
  ck_assert_int_eq(res, 1);
}
END_TEST

START_TEST(s21_division_21) {
  s21_decimal src1, src2, origin;
  // src1 = -7986567986895452.79851547;
  // src2 = 0.000000000000038;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11001111001110010100110000011011;
  src1.bits[1] = 0b01000101100101010101111100010001;
  src1.bits[2] = 0b00000000000000001010100100011111;
  src1.bits[3] = 0b10000000000010000000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b00000000000000000000000000100110;
  src2.bits[1] = 0b00000000000000000000000000000000;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b00000000000011110000000000000000;
  s21_decimal result = s21_div(src1, src2);
  origin.value_type = S21_NEGATIVE_INFINITY;
  origin.bits[0] = 0b00000000000000000000000000000000;
  origin.bits[1] = 0b00000000000000000000000000000000;
  origin.bits[2] = 0b00000000000000000000000000000000;
  origin.bits[3] = 0b00000000000000000000000000000000;
  ck_assert_int_eq(origin.bits[3], result.bits[3]);
  ck_assert_int_eq(origin.bits[2], result.bits[2]);
  ck_assert_int_eq(origin.bits[1], result.bits[1]);
  ck_assert_int_eq(origin.bits[0], result.bits[0]);
  ck_assert_int_eq(origin.value_type, result.value_type);
}
END_TEST

START_TEST(s21_mod_random_test) {
  int i, num1, num2;
  s21_decimal number1, number2, res1, res2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000), num2 = random_int(5000);
    valToLog("s21_mod", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_mod, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_mod, num 2", number2);
    res1 = s21_mod(number1, number2);
    decToLog("function: s21_mod, res 1", res1);
    s21_from_int_to_decimal(fmod(num1, num2), &res2);
    decToLog("function: s21_mod, res 2", res2);
    writeLog("------------");
    ck_assert_int_eq(dec_eq(res1, res2), 1);
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(100000), num2 = random_int(5000) * -1;
    valToLog("s21_mod", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_mod, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_mod, num 2", number2);
    res1 = s21_mod(number1, number2);
    decToLog("function: s21_mod, res 1", res1);
    s21_from_int_to_decimal(num1 % num2, &res2);
    decToLog("function: s21_mod, res 2", res2);
    writeLog("------------");
    ck_assert_int_eq(dec_eq(res1, res2), 1);
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_mod_1) {
  s21_decimal src1, src2, res_mod;
  int a = 3;
  int b = 2;
  int res_origin = a % b;
  int res = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_int(res_mod, &res);
  ck_assert_int_eq(res_origin, res);
}
END_TEST

START_TEST(s21_mod_2) {
  s21_decimal src1, src2, res_mod;
  int a = -98765;
  int b = 1234;
  int res_origin = a % b;
  int res = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_int(res_mod, &res);
  ck_assert_int_eq(res_origin, res);
}
END_TEST

START_TEST(s21_mod_3) {
  s21_decimal src1, src2, res_mod;
  int a = 30198;
  int b = 20210;
  int res_origin = a % b;
  int res = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_int(res_mod, &res);
  ck_assert_int_eq(res_origin, res);
}
END_TEST

START_TEST(s21_mod_4) {
  s21_decimal src1, src2, res_mod;
  int a = -98765;
  int b = -1234;
  int res_origin = a % b;
  int res = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_int(res_mod, &res);
  ck_assert_int_eq(res_origin, res);
}
END_TEST

START_TEST(s21_mod_5) {
  s21_decimal src1, src2, res_mod;
  int a = 98765;
  int b = 127234;
  int res_origin = a % b;
  int res = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_int(res_mod, &res);
  ck_assert_int_eq(res_origin, res);
}
END_TEST

START_TEST(s21_mod_6) {
  s21_decimal src1, src2, res_mod;
  int a = 342576;
  int b = 1542134;
  int res_origin = a % b;
  int res = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_int(res_mod, &res);
  ck_assert_int_eq(res_origin, res);
}
END_TEST

START_TEST(s21_mod_7) {
  s21_decimal src1, src2, res_mod;
  float a = 1.2;
  float b = 0.3;
  float res_origin = fmod(a, b);
  float res = 0.0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_float(res_mod, &res);
  ck_assert_float_eq(res_origin, res);
}
END_TEST

START_TEST(s21_mod_8) {
  s21_decimal src1, src2, res_mod;
  float a = 1.2;
  int b = 3;
  float res_origin = fmod(a, b);
  float res = 0;
  s21_from_float_to_decimal(a, &src1);
  s21_from_int_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_float(res_mod, &res);
  ck_assert_float_eq(res_origin, res);
}
END_TEST

START_TEST(s21_mod_9) {
  s21_decimal src1, src2, res_mod;
  int a = 342576;
  float b = INFINITY;
  int res = 0;
  s21_from_int_to_decimal(a, &src1);
  s21_from_float_to_decimal(b, &src2);
  res_mod = s21_mod(src1, src2);
  s21_from_decimal_to_int(res_mod, &res);
  ck_assert_int_eq(a, res);
}
END_TEST

START_TEST(s21_mod_10) {
  // 70000000000000000000000000000
  s21_decimal src1 = {{
        0b01110000000000000000000000000000,
        0b10110011000000110001000010100111,
        0b11100010001011101010010010010011,
        0b00000000000000000000000000000000
    }, S21_NORMAL_VALUE};

  // 0.001
  s21_decimal src2 = {{
        0b00000000000000000000000000000001,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000110000000000000000
    }, S21_NORMAL_VALUE};
  // 0.000
  s21_decimal res_orig = {{
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000000000000000000000,
        0b00000000000000110000000000000000
    }, S21_NORMAL_VALUE};

  s21_decimal res_mod = s21_mod(src1, src2);

  ck_assert_int_eq(res_orig.bits[3], res_mod.bits[3]);
  ck_assert_int_eq(res_orig.bits[2], res_mod.bits[2]);
  ck_assert_int_eq(res_orig.bits[1], res_mod.bits[1]);
  ck_assert_int_eq(res_orig.bits[0], res_mod.bits[0]);
  ck_assert_int_eq(res_orig.value_type, res_mod.value_type);
}
END_TEST

START_TEST(s21_mod_11) {
  s21_decimal src1 = DEC_ZERO;
  src1.value_type = S21_NAN;
  s21_decimal src2 = DEC_ZERO;
  s21_decimal res_orig = src1;

  s21_decimal res_mod = s21_mod(src1, src2);

  ck_assert_int_eq(res_orig.bits[3], res_mod.bits[3]);
  ck_assert_int_eq(res_orig.bits[2], res_mod.bits[2]);
  ck_assert_int_eq(res_orig.bits[1], res_mod.bits[1]);
  ck_assert_int_eq(res_orig.bits[0], res_mod.bits[0]);
  ck_assert_int_eq(res_orig.value_type, res_mod.value_type);

  src1.value_type = S21_NEGATIVE_INFINITY;
  res_mod = s21_mod(src1, src2);
  ck_assert_int_eq(res_orig.bits[3], res_mod.bits[3]);
  ck_assert_int_eq(res_orig.bits[2], res_mod.bits[2]);
  ck_assert_int_eq(res_orig.bits[1], res_mod.bits[1]);
  ck_assert_int_eq(res_orig.bits[0], res_mod.bits[0]);
  ck_assert_int_eq(res_orig.value_type, res_mod.value_type);
}
END_TEST

START_TEST(s21_is_less_random_test) {
  int i, res;
  s21_decimal number1, number2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    float num1 = random_float(), num2 = random_float();
    valfToLog("s21_is_less", num1, num2);
    s21_from_float_to_decimal(num1, &number1);
    decToLog("function: s21_is_less, num 1", number1);
    s21_from_float_to_decimal(num2, &number2);
    decToLog("function: s21_is_less, num 2", number2);
    res = s21_is_less(number1, number2);

    ck_assert_int_eq(res, !(num1 < num2));
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    int num1i = random_int(1000000) * -1, num2i = random_int(1000000) * -1;
    valToLog("s21_is_less", num1i, num2i);
    s21_from_int_to_decimal(num1i, &number1);
    decToLog("function: s21_is_less, num 1", number1);
    s21_from_int_to_decimal(num2i, &number2);
    decToLog("function: s21_is_less, num 2", number2);
    res = s21_is_less(number1, number2);

    ck_assert_int_eq(res, !(num1i < num2i));
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_is_less_test1) {
  s21_decimal dst1, dst2;

  s21_from_float_to_decimal(1.2345, &dst1);
  s21_from_float_to_decimal(1.2, &dst2);
  ck_assert_int_eq(s21_is_less(dst1, dst2), FALSE);  // 1.2345 < 1.2
  ck_assert_int_eq(s21_is_less(dst2, dst1), TRUE);   // 1.2 < 1.2345

  dst1 = s21_negate(dst1);
  dst2 = s21_negate(dst2);
  ck_assert_int_eq(s21_is_less(dst1, dst2), TRUE);   // -1.2345 < -1.2
  ck_assert_int_eq(s21_is_less(dst2, dst1), FALSE);  // -1.2 < -1.2345

  dst1 = s21_negate(dst1);
  ck_assert_int_eq(s21_is_less(dst1, dst2), FALSE);  //  1.2345 < -1.2 fail
  ck_assert_int_eq(s21_is_less(dst2, dst1), TRUE);   //  -1.2 < 1.2345 fail

  s21_from_float_to_decimal(0.0, &dst1);
  s21_from_float_to_decimal(0.0, &dst2);
  ck_assert_int_eq(s21_is_less(dst1, dst2), FALSE);  // 0 < 0

  dst1.value_type = S21_INFINITY;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_less(dst1, dst2), FALSE);  // +INFINITY < 0
  ck_assert_int_eq(s21_is_less(dst2, dst1), TRUE);   // 0 < +INFINITY

  dst1.value_type = S21_NEGATIVE_INFINITY;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_less(dst1, dst2), TRUE);   // -INFINITY < 0
  ck_assert_int_eq(s21_is_less(dst2, dst1), FALSE);  // 0 < -INFINITY
  dst2.value_type = S21_INFINITY;
  ck_assert_int_eq(s21_is_less(dst1, dst2), TRUE);  // -INFINITY < INFINITY
}
END_TEST

START_TEST(s21_is_less_test2) {
  s21_decimal src1, src2;
  int origin;
  // src1 = 0;
  // src2 = -23565454545435.156764546545455;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00000000000000000000000000000000;
  src1.bits[1] = 0b00000000000000000000000000000000;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000000000000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b11101101000010111011011100101111;
  src2.bits[1] = 0b10110000001111101110110000010010;
  src2.bits[2] = 0b01001100001001001110001100011010;
  src2.bits[3] = 0b10000000000011110000000000000000;
  int result = s21_is_less(src1, src2);
  origin = 1;
  ck_assert_int_eq(origin, result);
}
END_TEST

START_TEST(s21_is_less_test3) {
  s21_decimal src1, src2;
  int origin;
  // src1 = -2.514264337593543;
  // src2 = -2.514264337593542;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11001000101101101011010011000111;
  src1.bits[1] = 0b00000000000010001110111010110101;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b10000000000011110000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b11001000101101101011010011000110;
  src2.bits[1] = 0b00000000000010001110111010110101;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b10000000000011110000000000000000;
  int result = s21_is_less(src1, src2);
  origin = 0;
  ck_assert_int_eq(origin, result);
}
END_TEST

START_TEST(s21_is_less_test4) {
  s21_decimal src1, src2;
  int origin;
  // src1 = -754554545454658.97816770;
  // src2 = -754554545454658.9781677;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00100000101101101001001011000010;
  src1.bits[1] = 0b01110010110010011000000011111000;
  src1.bits[2] = 0b00000000000000000000111111111010;
  src1.bits[3] = 0b10000000000010000000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b10011100110111110000111010101101;
  src2.bits[1] = 0b00001011011110101000110011100101;
  src2.bits[2] = 0b00000000000000000000000110011001;
  src2.bits[3] = 0b10000000000001110000000000000000;
  int result = s21_is_less(src1, src2);
  origin = 1;
  ck_assert_int_eq(origin, result);

  // src1 = -579895323215489956.67897455465;
  // src2 = -579895323215489956.67897455465;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11100110001001011001001101101001;
  src1.bits[1] = 0b00111000110110101110001010110100;
  src1.bits[2] = 0b10111011010111111101000100011110;
  src1.bits[3] = 0b10000000000010110000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b11100110001001011001001101101001;
  src2.bits[1] = 0b00111000110110101110001010110100;
  src2.bits[2] = 0b10111011010111111101000100011110;
  src2.bits[3] = 0b10000000000010110000000000000000;
  result = s21_is_less(src1, src2);
  origin = 1;
  ck_assert_int_eq(origin, result);
}
END_TEST

START_TEST(s21_is_less_test5) {
  s21_decimal src1, src2;
  int origin;
  // src1 = -79228162514264337593543950335;
  // src2 = -792281625.14264337593543950335;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11111111111111111111111111111111;
  src1.bits[1] = 0b11111111111111111111111111111111;
  src1.bits[2] = 0b11111111111111111111111111111111;
  src1.bits[3] = 0b10000000000000000000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b11111111111111111111111111111111;
  src2.bits[1] = 0b11111111111111111111111111111111;
  src2.bits[2] = 0b11111111111111111111111111111111;
  src2.bits[3] = 0b10000000000101000000000000000000;
  int result = s21_is_less(src1, src2);
  origin = 0;
  ck_assert_int_eq(origin, result);
}
END_TEST

START_TEST(s21_is_less_test6) {
  s21_decimal src1, src2;
  int origin;
  // src1 = 79228162514264337593543950335;
  // src2 = -79228162514264337593543950335;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11111111111111111111111111111111;
  src1.bits[1] = 0b11111111111111111111111111111111;
  src1.bits[2] = 0b11111111111111111111111111111111;
  src1.bits[3] = 0b00000000000000000000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b11111111111111111111111111111111;
  src2.bits[1] = 0b11111111111111111111111111111111;
  src2.bits[2] = 0b11111111111111111111111111111111;
  src2.bits[3] = 0b10000000000000000000000000000000;
  int result = s21_is_less(src1, src2);
  origin = 1;
  ck_assert_int_eq(origin, result);
}
END_TEST

START_TEST(s21_is_less_test7) {
  s21_decimal src1, src2;
  int origin;
  // src1 = -69.1234567;
  // src2 = -69.12345670000000;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00101001001100110110011100000111;
  src1.bits[1] = 0b00000000000000000000000000000000;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b10000000000001110000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b11100100001110011001110110000000;
  src2.bits[1] = 0b00000000000110001000111010111101;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b10000000000011100000000000000000;
  int result = s21_is_less(src1, src2);
  origin = 1;
  ck_assert_int_eq(origin, result);

  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00000000000000000000000000000000;
  src1.bits[1] = 0b00000000000000000000000000000000;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000000010000000000000000;
  src2.value_type = S21_NORMAL_VALUE;
  src2.bits[0] = 0b00000000000000000000000001000101;
  src2.bits[1] = 0b00000000000000000000000000000000;
  src2.bits[2] = 0b00000000000000000000000000000000;
  src2.bits[3] = 0b00000000000000100000000000000000;
  result = s21_is_less(src1, src2);
  origin = 0;
  ck_assert_int_eq(origin, result);
}
END_TEST

START_TEST(s21_is_less_test8) {
  s21_decimal src1 = DEC_MAX, src2 = DEC_MAX;
  int origin = 0;
  // src1 = 792281625142643375935439503.35;
  // src2 = 7922816251426433759354395033.5;
  set_scale(&src1, 2);
  set_scale(&src2, 1);
  int result = s21_is_less(src1, src2);
  ck_assert_int_eq(origin, result);
}
END_TEST


START_TEST(s21_is_less_or_equal_random_test) {
  int i, num1, num2, res;
  s21_decimal number1, number2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000), num2 = random_int(1000000);
    valToLog("s21_is_less_or_equal", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_less_or_equal, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_less_or_equal, num 2", number2);
    res = s21_is_less_or_equal(number1, number2);

    ck_assert_int_eq(res, !(num1 <= num2));

    writeLog("num1 == num1");
    res = s21_is_less_or_equal(number1, number1);

    ck_assert_int_eq(res, 0);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000) * -1, num2 = random_int(1000000) * -1;
    valToLog("s21_is_less_or_equal", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_less_or_equal, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_less_or_equal, num 2", number2);
    res = s21_is_less_or_equal(number1, number2);

    ck_assert_int_eq(res, !(num1 <= num2));
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    float num1f = random_float(), num2f = random_float();
    valfToLog("s21_is_less_or_equal", num1f, num2f);
    s21_from_float_to_decimal(num1f, &number1);
    decToLog("function: s21_is_less_or_equal, num 1", number1);
    s21_from_float_to_decimal(num2f, &number2);
    decToLog("function: s21_is_less_or_equal, num 2", number2);
    res = s21_is_less_or_equal(number1, number2);

    ck_assert_int_eq(res, !(num1f <= num2f));
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_is_less_or_equal_test) {
  s21_decimal dst1, dst2;

  s21_from_float_to_decimal(1.2345, &dst1);
  s21_from_float_to_decimal(1.2, &dst2);
  ck_assert_int_eq(s21_is_less_or_equal(dst1, dst2), FALSE);  // 1.2345 <= 1.2
  ck_assert_int_eq(s21_is_less_or_equal(dst2, dst1), TRUE);   // 1.2 <= 1.2345

  dst1 = s21_negate(dst1);
  dst2 = s21_negate(dst2);
  ck_assert_int_eq(s21_is_less_or_equal(dst1, dst2),
                   TRUE);  // -1.2345 <= -1.2
  ck_assert_int_eq(s21_is_less_or_equal(dst2, dst1),
                   FALSE);  // -1.2 <= 1.2345

  dst1 = s21_negate(dst1);
  ck_assert_int_eq(s21_is_less_or_equal(dst1, dst2),
                   FALSE);  //  1.2345 <= -1.2 // fail
  ck_assert_int_eq(s21_is_less_or_equal(dst2, dst1),
                   TRUE);  //  -1.2 <= 1.2345

  s21_from_float_to_decimal(0.0, &dst1);
  s21_from_float_to_decimal(0.0, &dst2);
  ck_assert_int_eq(s21_is_less_or_equal(dst1, dst2), TRUE);  // 0 <= 0

  dst1.value_type = S21_INFINITY;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_less_or_equal(dst1, dst2),
                   FALSE);                                   // +INFINITY <= 0
  ck_assert_int_eq(s21_is_less_or_equal(dst2, dst1), TRUE);  // 0 <= +INFINITY

  dst1.value_type = S21_INFINITY;
  dst2.value_type = S21_INFINITY;
  ck_assert_int_eq(s21_is_less_or_equal(dst2, dst1),
                   TRUE);  // +INFINITY <= +INFINITY

  dst1.value_type = S21_NEGATIVE_INFINITY;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_less_or_equal(dst1, dst2), TRUE);  // -INFINITY <= 0
  ck_assert_int_eq(s21_is_less_or_equal(dst2, dst1),
                   FALSE);  // 0 <= -INFINITY

  s21_from_float_to_decimal(1726.73, &dst1);
  s21_from_float_to_decimal(1726.73, &dst2);
  ck_assert_int_eq(s21_is_less_or_equal(dst1, dst2),
                   TRUE);  // 1726.73 <= 1726.73
}
END_TEST

START_TEST(s21_is_greater_random_test) {
  int i, num1, num2, res;
  s21_decimal number1, number2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000), num2 = random_int(1000000);
    valToLog("s21_is_greater", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_greater, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_greater, num 2", number2);
    res = s21_is_greater(number1, number2);

    ck_assert_int_eq(res, !(num1 > num2));
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000) * -1, num2 = random_int(1000000) * -1;
    valToLog("s21_is_greater", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_greater, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_greater, num 2", number2);
    res = s21_is_greater(number1, number2);

    ck_assert_int_eq(res, !(num1 > num2));
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    float num1f = random_float(), num2f = random_float();
    valfToLog("s21_is_greater", num1f, num2f);
    s21_from_float_to_decimal(num1f, &number1);
    decToLog("function: s21_is_greater, num 1", number1);
    s21_from_float_to_decimal(num2f, &number2);
    decToLog("function: s21_is_greater, num 2", number2);
    res = s21_is_greater(number1, number2);

    ck_assert_int_eq(res, !(num1f > num2f));
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_is_greater_test) {
  s21_decimal dst1, dst2;

  s21_from_float_to_decimal(1.2345, &dst1);
  s21_from_float_to_decimal(1.2, &dst2);
  ck_assert_int_eq(s21_is_greater(dst1, dst2), TRUE);   // 1.2345 > 1.2
  ck_assert_int_eq(s21_is_greater(dst2, dst1), FALSE);  // 1.2 > 1.2345

  dst1 = s21_negate(dst1);
  dst2 = s21_negate(dst2);
  ck_assert_int_eq(s21_is_greater(dst1, dst2), FALSE);  // -1.2345 > -1.2
  ck_assert_int_eq(s21_is_greater(dst2, dst1), TRUE);   // -1.2 > 1.2345

  dst1 = s21_negate(dst1);
  ck_assert_int_eq(s21_is_greater(dst1, dst2), TRUE);   //  1.2345 > -1.2
  ck_assert_int_eq(s21_is_greater(dst2, dst1), FALSE);  //  -1.2 > 1.2345

  s21_from_float_to_decimal(0.0, &dst1);
  s21_from_float_to_decimal(0.0, &dst2);
  ck_assert_int_eq(s21_is_greater(dst1, dst2), FALSE);  // 0 > 0

  dst1.value_type = S21_INFINITY;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_greater(dst1, dst2), TRUE);   // +INFINITY > 0
  ck_assert_int_eq(s21_is_greater(dst2, dst1), FALSE);  // 0 > +INFINITY
  dst1.value_type = S21_NAN;
  ck_assert_int_eq(s21_is_greater(dst2, dst1), FALSE);  // 0 > NAN

  dst1.value_type = S21_NEGATIVE_INFINITY;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_greater(dst1, dst2), FALSE);  // -INFINITY > 0
  ck_assert_int_eq(s21_is_greater(dst2, dst1), TRUE);   // 0 > -INFINITY
}
END_TEST

START_TEST(s21_is_greater_or_equal_random_test) {
  int i, num1, num2, res;
  s21_decimal number1, number2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000), num2 = random_int(1000000);
    valToLog("s21_is_greater_or_equal", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_greater_or_equal, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_greater_or_equal, num 2", number2);
    res = s21_is_greater_or_equal(number1, number2);

    ck_assert_int_eq(res, !(num1 >= num2));

    writeLog("num1 == num1");
    res = s21_is_greater_or_equal(number1, number1);

    ck_assert_int_eq(res, 0);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000) * -1, num2 = random_int(1000000) * -1;
    valToLog("s21_is_greater_or_equal", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_greater_or_equal, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_greater_or_equal, num 2", number2);
    res = s21_is_greater_or_equal(number1, number2);

    ck_assert_int_eq(res, !(num1 >= num2));

    writeLog("num1 == num1");
    res = s21_is_greater_or_equal(number1, number1);

    ck_assert_int_eq(res, 0);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    float num1f = random_float(), num2f = random_float();
    valfToLog("s21_is_greater_or_equal", num1f, num2f);
    s21_from_float_to_decimal(num1f, &number1);
    decToLog("function: s21_is_greater_or_equal, num 1", number1);
    s21_from_float_to_decimal(num2f, &number2);
    decToLog("function: s21_is_greater_or_equal, num 2", number2);
    res = s21_is_greater_or_equal(number1, number2);

    ck_assert_int_eq(res, !(num1f >= num2f));

    writeLog("num1 == num1");
    res = s21_is_greater_or_equal(number1, number1);

    ck_assert_int_eq(res, 0);
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_is_greater_or_equal_test) {
  s21_decimal dst1, dst2;

  s21_from_float_to_decimal(1.2345, &dst1);
  s21_from_float_to_decimal(1.2, &dst2);
  ck_assert_int_eq(s21_is_greater_or_equal(dst1, dst2),
                   TRUE);  // 1.2345 >= 1.2
  ck_assert_int_eq(s21_is_greater_or_equal(dst2, dst1),
                   FALSE);  // 1.2 >= 1.2345

  dst1 = s21_negate(dst1);
  dst2 = s21_negate(dst2);
  ck_assert_int_eq(s21_is_greater_or_equal(dst1, dst2),
                   FALSE);  // -1.2345 >= -1.2
  ck_assert_int_eq(s21_is_greater_or_equal(dst2, dst1),
                   TRUE);  // -1.2 >= 1.2345

  dst1 = s21_negate(dst1);
  ck_assert_int_eq(s21_is_greater_or_equal(dst1, dst2),
                   TRUE);  //  1.2345 >= -1.2 // fail
  ck_assert_int_eq(s21_is_greater_or_equal(dst2, dst1),
                   FALSE);  //  -1.2 >= 1.2345

  s21_from_float_to_decimal(0.0, &dst1);
  s21_from_float_to_decimal(0.0, &dst2);
  ck_assert_int_eq(s21_is_greater_or_equal(dst1, dst2), TRUE);  // 0 >= 0

  dst1.value_type = S21_INFINITY;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_greater_or_equal(dst1, dst2),
                   TRUE);  // +INFINITY >= 0
  ck_assert_int_eq(s21_is_greater_or_equal(dst2, dst1),
                   FALSE);  // 0 >= +INFINITY

  dst1.value_type = S21_NEGATIVE_INFINITY;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_greater_or_equal(dst1, dst2),
                   FALSE);  // -INFINITY >= 0
  ck_assert_int_eq(s21_is_greater_or_equal(dst2, dst1),
                   TRUE);  // 0 >= -INFINITY
}
END_TEST

START_TEST(s21_is_equal_random_test) {
  int i, num1, num2, res;
  s21_decimal number1, number2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000), num2 = random_int(1000000);
    valToLog("s21_is_equal", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_equal, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_equal, num 2", number2);
    res = s21_is_equal(number1, number2);
    ck_assert_int_eq(res, !(num1 == num2));
    writeLog("num1 == num1");
    res = s21_is_equal(number1, number1);
    ck_assert_int_eq(res, 0);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000) * -1, num2 = random_int(1000000) * -1;
    valToLog("s21_is_equal", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_equal, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_equal, num 2", number2);
    res = s21_is_equal(number1, number2);
    ck_assert_int_eq(res, !(num1 == num2));
    writeLog("num1 == num1");
    res = s21_is_equal(number1, number1);
    ck_assert_int_eq(res, 0);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    float num1f = random_float(), num2f = random_float();
    valfToLog("s21_is_equal", num1f, num2f);
    s21_from_float_to_decimal(num1f, &number1);
    decToLog("function: s21_is_equal, num 1", number1);
    s21_from_float_to_decimal(num2f, &number2);
    decToLog("function: s21_is_equal, num 2", number2);
    res = s21_is_equal(number1, number2);
    ck_assert_int_eq(res, !(num1f == num2f));
    writeLog("num1 == num1");
    res = s21_is_equal(number1, number1);
    ck_assert_int_eq(res, 0);
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_is_equal_test) {
  s21_decimal dst1, dst2;

  s21_from_float_to_decimal(1.2345, &dst1);
  s21_from_float_to_decimal(1.2, &dst2);
  ck_assert_int_eq(s21_is_equal(dst1, dst2), FALSE);  // 1.2345 = 1.2

  s21_from_float_to_decimal(1.2, &dst1);
  s21_from_float_to_decimal(1.2, &dst2);
  dst1.value_type = S21_NEGATIVE_INFINITY;
  dst2.value_type = S21_NEGATIVE_INFINITY;
  ck_assert_int_eq(s21_is_equal(dst1, dst2), TRUE);  // 1.2 = 1.2

  s21_from_float_to_decimal(-234.17, &dst1);
  s21_from_float_to_decimal(234.17, &dst2);
  ck_assert_int_eq(s21_is_equal(dst1, dst2), FALSE);

  s21_from_float_to_decimal(234.17, &dst1);
  s21_from_float_to_decimal(234.17, &dst2);
  ck_assert_int_eq(s21_is_equal(dst1, dst2), TRUE);

  dst1.value_type = S21_NORMAL_VALUE;
  dst2.value_type = S21_NORMAL_VALUE;
  ck_assert_int_eq(s21_is_less_or_equal(dst2, dst1),
                   TRUE);  // +INFINITY = +INFINITY

  s21_from_int_to_decimal(0, &dst1);  // -0 == 0
  s21_from_int_to_decimal(0, &dst2);
  dst1.bits[3] = SIGNMASK;
  ck_assert_int_eq(s21_is_equal(dst1, dst2), TRUE);

  s21_from_int_to_decimal(0, &dst1);  // NAN == NAN
  s21_from_int_to_decimal(0, &dst2);
  dst1.value_type = S21_NAN;
  dst2.value_type = S21_NAN;
  ck_assert_int_eq(s21_is_equal(dst1, dst2), FALSE);
}
END_TEST

START_TEST(s21_is_not_equal_random_test) {
  int i, num1, num2, res;
  s21_decimal number1, number2;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000), num2 = random_int(1000000);
    valToLog("s21_is_not_equal", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_not_equal, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_not_equal, num 2", number2);
    res = s21_is_not_equal(number1, number2);
    ck_assert_int_eq(res, !(num1 != num2));
    writeLog("num1 == num1");
    res = s21_is_not_equal(number1, number1);
    ck_assert_int_eq(res, 1);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num1 = random_int(1000000) * -1, num2 = random_int(1000000) * -1;
    valToLog("s21_is_not_equal", num1, num2);
    s21_from_int_to_decimal(num1, &number1);
    decToLog("function: s21_is_not_equal, num 1", number1);
    s21_from_int_to_decimal(num2, &number2);
    decToLog("function: s21_is_not_equal, num 2", number2);
    res = s21_is_not_equal(number1, number2);
    ck_assert_int_eq(res, !(num1 != num2));
    writeLog("num1 == num1");
    res = s21_is_not_equal(number1, number1);
    ck_assert_int_eq(res, 1);
    writeLog("------------");
  }
  writeLog("----- next -----");

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    float num1f = random_float(), num2f = random_float();
    valfToLog("s21_is_not_equal", num1f, num2f);
    s21_from_float_to_decimal(num1f, &number1);
    decToLog("function: s21_is_not_equal, num 1", number1);
    s21_from_float_to_decimal(num2f, &number2);
    decToLog("function: s21_is_not_equal, num 2", number2);
    res = s21_is_not_equal(number1, number2);
    ck_assert_int_eq(res, !(num1f != num2f));
    writeLog("num1 == num1");
    res = s21_is_not_equal(number1, number1);
    ck_assert_int_eq(res, 1);
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_is_not_equal_test) {
  s21_decimal dst1, dst2;

  s21_from_float_to_decimal(1.2345, &dst1);
  s21_from_float_to_decimal(1.2, &dst2);
  ck_assert_int_eq(s21_is_not_equal(dst1, dst2), TRUE);  // 1.2345 = 1.2

  s21_from_float_to_decimal(1.2, &dst1);
  s21_from_float_to_decimal(1.2, &dst2);
  ck_assert_int_eq(s21_is_not_equal(dst1, dst2), FALSE);  // 1.2 = 1.2

  s21_from_float_to_decimal(-234.17, &dst1);
  s21_from_float_to_decimal(234.17, &dst2);
  dst1.value_type = S21_NEGATIVE_INFINITY;
  dst2.value_type = S21_NEGATIVE_INFINITY;
  ck_assert_int_eq(s21_is_not_equal(dst1, dst2), FALSE);

  s21_from_float_to_decimal(234.17, &dst1);
  s21_from_float_to_decimal(234.17, &dst2);
  ck_assert_int_eq(s21_is_not_equal(dst1, dst2), FALSE);
}
END_TEST

START_TEST(s21_from_int_to_decimal_random_test) {
  int i, num, res;
  s21_decimal number, one = DEC_ONE;

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num = random_int(9999999);
    valToLog("s21_from_int_to_decimal", num, 0);
    res = s21_from_int_to_decimal(num, &number);
    if (res == 0) {
      decToLog("function: s21_from_int_to_decimal, num", number);
      ck_assert_int_eq(res, 0);
    }
    writeLog("------------");

    num = random_int(9999999) * -1;
    valToLog("s21_from_int_to_decimal", num, 0);
    res = s21_from_int_to_decimal(num, &number);
    if (res == 0) {
      decToLog("function: s21_from_int_to_decimal, num", number);
      ck_assert_int_eq(res, 0);
    }
    writeLog("------------");
  }

  res = s21_from_int_to_decimal(num, NULL);
  ck_assert_int_eq(res, 1);
  writeLog("------------");

  res = s21_from_int_to_decimal(1, &number);
  ck_assert_int_eq(dec_eq(number, one), 1);
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_from_int_to_decimal_test) {
  s21_decimal val;

  s21_from_int_to_decimal(0, &val);
  ck_assert_int_eq(val.bits[0], 0);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 0);

  s21_from_int_to_decimal(-128, &val);
  ck_assert_int_eq(val.bits[0], 128);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], -2147483648);

  s21_from_int_to_decimal(127, &val);
  ck_assert_int_eq(val.bits[0], 127);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 0);

  s21_from_int_to_decimal(-2147483648, &val);
  ck_assert_int_eq(val.bits[0], -2147483648);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], -2147483648);

  s21_from_int_to_decimal(2147483647, &val);
  ck_assert_int_eq(val.bits[0], 2147483647);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 0);
}
END_TEST

START_TEST(s21_from_float_to_decimal_random_test) {
  int i, res;
  float num;
  s21_decimal number;

  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    num = random_float();
    valfToLog("s21_from_float_to_decimal", num, 0);
    res = s21_from_float_to_decimal(num, &number);
    // if (res == 0) {
    decToLog("function: s21_from_float_to_decimal, num", number);
    ck_assert_int_eq(res, 0);
    // }
    writeLog("------------");

    num = random_float() * -1;
    valToLog("s21_from_float_to_decimal", num, 0);
    res = s21_from_float_to_decimal(num, &number);
    // if (res == 0) {
    decToLog("function: s21_from_float_to_decimal, num", number);
    ck_assert_int_eq(res, 0);
    // }
    writeLog("------------");
  }

  writeLog("s21_from_float_to_decimal: INFINITY");
  res = s21_from_float_to_decimal(INFINITY, &number);
  ck_assert_int_eq(res, 1);
  writeLog("------------");

  writeLog("s21_from_float_to_decimal: -INFINITY");
  res = s21_from_float_to_decimal(-INFINITY, &number);
  ck_assert_int_eq(res, 1);
  writeLog("------------");

  writeLog("s21_from_float_to_decimal: NAN");
  res = s21_from_float_to_decimal(NAN, &number);
  ck_assert_int_eq(res, 1);
  writeLog("------------");

  valfToLog("s21_from_float_to_decimal", 7.9e29, 0);
  res = s21_from_float_to_decimal(7.9e29, &number);
  ck_assert_int_eq(res, 1);
  writeLog("------------");

  valfToLog("s21_from_float_to_decimal", 1e-28, 0);
  res = s21_from_float_to_decimal(1e-28, &number);
  ck_assert_int_eq(res, 1);
  writeLog("------------");

  writeLog("s21_from_float_to_decimal: NULL pointer");
  res = s21_from_float_to_decimal(num, NULL);
  ck_assert_int_eq(res, 1);
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_from_float_to_decimal_1) {
  s21_decimal val;

  s21_from_float_to_decimal(0.03, &val);
  ck_assert_int_eq(val.bits[0], 3);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 131072);

  s21_from_float_to_decimal(127.1234, &val);
  ck_assert_int_eq(val.bits[0], 1271234);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 262144);
}
END_TEST

START_TEST(s21_from_float_to_decimal_2) {
  s21_decimal val;
  s21_from_float_to_decimal(-128.023, &val);
  ck_assert_int_eq(val.bits[0], 12802299);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], -2147155968);
}
END_TEST

START_TEST(s21_from_float_to_decimal_3) {
  s21_decimal val;
  s21_from_float_to_decimal(-2.1474836E+09, &val);
  ck_assert_int_eq(val.bits[0], -2147483648);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], -2147483648);
}
END_TEST

START_TEST(s21_from_float_to_decimal_4) {
  s21_decimal val;
  s21_from_float_to_decimal(22.14836E+03, &val);
  ck_assert_int_eq(val.bits[0], 2214836);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 131072);
}
END_TEST

START_TEST(s21_from_float_to_decimal_5) {
  s21_decimal val;
  s21_from_float_to_decimal(1.02E+09, &val);
  ck_assert_int_eq(val.bits[0], 1020000000);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 0);
}
END_TEST

START_TEST(s21_from_float_to_decimal_6) {
  s21_decimal val;
  s21_from_float_to_decimal(-333.2222, &val);
  ck_assert_int_eq(val.bits[0], 3332222);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], -2147221504);
}
END_TEST

START_TEST(s21_from_float_to_decimal_7) {
  s21_decimal val;
  float a = INFINITY;
  s21_from_float_to_decimal(a, &val);
  ck_assert_int_eq(val.bits[0], 0);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 0);
}
END_TEST

START_TEST(s21_from_float_to_decimal_8) {
  s21_decimal val;
  float a = -INFINITY;
  s21_from_float_to_decimal(a, &val);
  ck_assert_int_eq(val.bits[0], 0);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 0);
}
END_TEST

START_TEST(s21_from_float_to_decimal_9) {
  s21_decimal val;
  float a = NAN;
  s21_from_float_to_decimal(a, &val);
  ck_assert_int_eq(val.bits[0], 0);
  ck_assert_int_eq(val.bits[1], 0);
  ck_assert_int_eq(val.bits[2], 0);
  ck_assert_int_eq(val.bits[3], 0);
}
END_TEST

START_TEST(s21_from_decimal_to_int_random_test) {
  int res, num;
  s21_decimal one = DEC_ONE, neg_one = DEC_MINUS_ONE,
              zero_one = DEC_ZERO_ONE, zero = DEC_ZERO, max = DEC_MAX;

  decToLog("function: s21_from_decimal_to_int, num", one);
  res = s21_from_decimal_to_int(one, &num);
  valToLog("s21_from_decimal_to_int", num, 0);
  ck_assert_int_eq(res, !(num == 1));
  writeLog("------------");

  decToLog("function: s21_from_decimal_to_int, num", neg_one);
  res = s21_from_decimal_to_int(neg_one, &num);
  valToLog("s21_from_decimal_to_int", num, 0);
  ck_assert_int_eq(res, !(num == -1));
  writeLog("------------");

  decToLog("function: s21_from_decimal_to_int, num", zero_one);
  res = s21_from_decimal_to_int(zero_one, &num);
  valToLog("s21_from_decimal_to_int", num, 0);
  ck_assert_int_eq(res, !(num == 0));
  writeLog("------------");

  decToLog("function: s21_from_decimal_to_int, num", zero);
  res = s21_from_decimal_to_int(zero, &num);
  valToLog("s21_from_decimal_to_int", num, 0);
  ck_assert_int_eq(res, !(num == 0));
  writeLog("------------");

  decToLog("function: s21_from_decimal_to_int, num", max);
  res = s21_from_decimal_to_int(max, &num);
  ck_assert_int_eq(res, 1);
  writeLog("------------");

  writeLog("function: s21_from_decimal_to_int, num, decimal: NULL");
  res = s21_from_decimal_to_int(max, NULL);
  ck_assert_int_eq(res, 1);
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_from_decimal_to_int_1) {
  s21_decimal src;
  int result = 0, number = 0;
  src.value_type = 0;
  src.bits[0] = INT_MAX;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = 0;
  result = s21_from_decimal_to_int(src, &number);
  ck_assert_float_eq(number, 2147483647);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_int_2) {
  s21_decimal src;
  int result = 0, number = 0;
  src.value_type = 0;
  src.bits[0] = 133141;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = 0;
  result = s21_from_decimal_to_int(src, &number);
  ck_assert_int_eq(number, 133141);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_int_3) {
  s21_decimal src;
  int result = 0, number = 0;
  src.value_type = 0;
  src.bits[0] = 2147483648;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = INT_MIN;
  result = s21_from_decimal_to_int(src, &number);
  ck_assert_int_eq(number, -2147483648);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_int_4) {
  s21_decimal src;
  int result = 0, number = 0;
  src.value_type = 0;
  src.bits[0] = 123451234;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = 2147483648;
  result = s21_from_decimal_to_int(src, &number);
  ck_assert_int_eq(number, -123451234);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_int_5) {
  s21_decimal src;
  int result = 0, number = 0;
  src.value_type = 0;
  src.bits[0] = 18;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = 2147483648;
  result = s21_from_decimal_to_int(src, &number);
  ck_assert_int_eq(number, -18);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_int_6) {
  s21_decimal src;
  int result = 0;
  int64_t number = 0;
  src.value_type = 0;
  src.bits[0] = 4294967295;
  src.bits[1] = 4294967295;
  src.bits[2] = 0;
  src.bits[3] = 0;
  result = s21_from_decimal_to_int64(src, &number);
  ck_assert_int_eq(number, 0xFFFFFFFFFFFFFFFF);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_float_random_test) {
  int res = -1;
  float num;
  s21_decimal number, max = DEC_MAX;

  for (int i = 0; i <= RANDOM_TEST_COUNT; i++) {
    float rand_val = random_int(100);
    valToLog("s21_from_decimal_to_float", rand_val, 0);
    if (s21_from_int_to_decimal(rand_val, &number) == 0) {
      decToLog("function: s21_from_decimal_to_float, num", number);
      res = s21_from_decimal_to_float(number, &num);
      ck_assert_double_eq(num, (float)rand_val);
      ck_assert_int_eq(res, 0);
    }
    writeLog("------------");

    rand_val *= -1;
    valToLog("s21_from_decimal_to_float", rand_val, 0);
    if (s21_from_int_to_decimal(rand_val, &number) == 0) {
      decToLog("function: s21_from_decimal_to_float, num", number);
      res = s21_from_decimal_to_float(number, &num);
      ck_assert_double_eq(num, (float)rand_val);
      ck_assert_int_eq(res, 0);
    }
    writeLog("------------");
  }

  decToLog("function: s21_from_decimal_to_float, num", max);
  max.bits[S] = random_int(28) << SCALESHIFT;
  res = s21_from_decimal_to_float(max, &num);
  ck_assert_int_eq(res, 0);
  writeLog("------------");

  writeLog("function: s21_from_decimal_to_int, num, decimal: NULL");
  res = s21_from_decimal_to_float(max, NULL);
  ck_assert_int_eq(res, 1);
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_from_decimal_to_float_1) {
  s21_decimal src;
  int result = 0;
  float number = 0.0;
  src.value_type = 0;
  src.bits[0] = 18122;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = 2147680256;
  result = s21_from_decimal_to_float(src, &number);
  ck_assert_float_eq(number, -18.122);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_float_2) {
  s21_decimal src;
  int result = 0;
  float number = 0.0;
  src.value_type = 0;
  src.bits[0] = 1812;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = 2147483648;
  result = s21_from_decimal_to_float(src, &number);
  ck_assert_float_eq(number, -1812);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_float_3) {
  s21_decimal src;
  int result = 0;
  float number = 0.0;
  src.value_type = 0;
  src.bits[0] = 0XFFFFFF;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = 0;
  result = s21_from_decimal_to_float(src, &number);
  ck_assert_float_eq(number, 16777215);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_float_4) {
  s21_decimal src;
  int result = 0;
  float number = 0.0;
  src.value_type = 0;
  src.bits[0] = 23450987;
  src.bits[1] = 0;
  src.bits[2] = 0;
  src.bits[3] = 2147745792;
  result = s21_from_decimal_to_float(src, &number);
  ck_assert_float_eq(number, -2345.0987);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_from_decimal_to_float_5) {
  s21_decimal src;
  int result = 0;
  float number = 0.0;
  src.value_type = 0;
  src.bits[0] = 4294967295;
  src.bits[1] = 4294967295;
  src.bits[2] = 0;
  src.bits[3] = 0;
  result = s21_from_decimal_to_float(src, &number);
  ck_assert_float_eq(number, 0xFFFFFFFFFFFFFFFF);
  ck_assert_int_eq(result, 0);
}
END_TEST

START_TEST(s21_floor_1) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00001111111111111111111111111111;
  src1.bits[1] = 0b00111110001001010000001001100001;
  src1.bits[2] = 0b00100000010011111100111001011110;
  src1.bits[3] = 0b00000000000010100000000000000000;
  s21_decimal res_od = s21_floor(src1);
  s21_decimal result;
  result.bits[0] = 0b10100111011000111111111111111111;
  result.bits[1] = 0b00001101111000001011011010110011;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b00000000000000000000000000000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_floor_2) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00001111111111111111111111111111;
  src1.bits[1] = 0b00111110001001010000001001100001;
  src1.bits[2] = 0b00100000010011111100111001011110;
  src1.bits[3] = 0b10000000000010100000000000000000;
  s21_decimal res_od = s21_floor(src1);
  s21_decimal result;
  result.bits[0] = 0b10100111011001000000000000000000;
  result.bits[1] = 0b00001101111000001011011010110011;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b10000000000000000000000000000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_floor_3) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b10111101001001111000010001010010;
  src1.bits[1] = 0b00000000000000000000000000011100;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b10000000000010010000000000000000;
  s21_decimal res_od = s21_floor(src1);
  s21_decimal result;
  result.bits[0] = 0b00000000000000000000000001111100;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b10000000000000000000000000000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_floor_4) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b10010011111100000001110001010010;
  src1.bits[1] = 0b00000000000000000000000100100000;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000010100000000000000000;
  s21_decimal res_od = s21_floor(src1);
  s21_decimal result;
  result.bits[0] = 0b00000000000000000000000001111011;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b00000000000000000000000000000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_floor_5) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b01010101001110101110101110110001;
  src1.bits[1] = 0b00001101101101001101101001011111;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b10000000000100100000000000000000;
  s21_decimal res_od = s21_floor(src1);
  s21_decimal result;
  result.bits[0] = 0b00000000000000000000000000000001;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b10000000000000000000000000000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_floor_6) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b01010101001110101110101110110001;
  src1.bits[1] = 0b00001101101101001101101001011111;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000100100000000000000000;
  s21_decimal res_od = s21_floor(src1);
  s21_decimal result;
  result.bits[0] = 0b00000000000000000000000000000000;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b00000000000000000000000000000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_floor_7) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b10010111011100111001111111111111;
  src1.bits[1] = 0b00111100000010000011000110001101;
  src1.bits[2] = 0b00000000000000000000000000000001;
  src1.bits[3] = 0b00000000000001110000000000000000;
  s21_decimal result = s21_floor(src1);
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0b00000000000000000000001000010010;
  result_origin.bits[0] = 0b00110110101101101000110000111111;
  ck_assert_int_eq(result_origin.bits[3], result.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result.bits[0]);
}
END_TEST

START_TEST(s21_floor_8) {
  s21_decimal src1;
  float a = NAN;
  s21_from_float_to_decimal(a, &src1);
  s21_decimal res_od = s21_floor(src1);
  ck_assert_float_eq(res_od.value_type, S21_NAN);
}
END_TEST

START_TEST(s21_round_1) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b01100011000011111111111111111111;
  src1.bits[1] = 0b01101011110001110101111000101101;
  src1.bits[2] = 0b00000000000000000000000000000101;
  src1.bits[3] = 0b10000000000010100000000000000000;
  s21_decimal result;
  result.bits[0] = 0b01010100000010111110010000000000;
  result.bits[1] = 0b00000000000000000000000000000010;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b10000000000000000000000000000000;
  s21_decimal res_od = s21_round(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_round_2) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b01010101001110101110101110110001;
  src1.bits[1] = 0b00001101101101001101101001011111;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b10000000000100100000000000000000;
  s21_decimal result;
  result.bits[0] = 0b00000000000000000000000000000001;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b10000000000000000000000000000000;
  s21_decimal res_od = s21_round(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_round_3) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b10010011111100000001110001010010;
  src1.bits[1] = 0b00000000000000000000000100100000;
  src1.bits[2] = 0b00000000000000000000000000000000;
  src1.bits[3] = 0b00000000000010100000000000000000;
  s21_decimal result;
  result.bits[0] = 0b00000000000000000000000001111100;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal res_od = s21_round(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_round_4) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11001101110001110111110001000000;
  src1.bits[1] = 0b00111110001001010000001001100000;
  src1.bits[2] = 0b00100000010011111100111001011110;
  src1.bits[3] = 0b10000000000001000000000000000000;
  s21_decimal result;
  result.bits[0] = 0b10100000111111100100111000000100;
  result.bits[1] = 0b00011011110011101100110011101101;
  result.bits[2] = 0b00000000000000001101001111000010;
  result.bits[3] = 0b10000000000000000000000000000000;
  s21_decimal res_od = s21_round(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_round_5) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b10100000111111100100111000000100;
  src1.bits[1] = 0b00011011110011101100110011101101;
  src1.bits[2] = 0b00000000000000001101001111000010;
  src1.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal res_od = s21_round(src1);
  s21_decimal result;
  result.bits[0] = 0b10100000111111100100111000000100;
  result.bits[1] = 0b00011011110011101100110011101101;
  result.bits[2] = 0b00000000000000001101001111000010;
  result.bits[3] = 0b00000000000000000000000000000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_round_6) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b10010111011100111001111111111111;
  src1.bits[1] = 0b00111100000010000011000110001101;
  src1.bits[2] = 0b00000000000000000000000000000001;
  src1.bits[3] = 0b00000000000001110000000000000000;
  s21_decimal res_od = s21_round(src1);
  s21_decimal result;
  result.bits[3] = 0;
  result.bits[2] = 0;
  result.bits[1] = 0b00000000000000000000001000010010;
  result.bits[0] = 0b00110110101101101000110001000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_round_7) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b10010111011100111001111111111111;
  src1.bits[1] = 0b00111100000010000011000110001101;
  src1.bits[2] = 0b00000000000000000000000000000001;
  src1.bits[3] = 0b10000000000001110000000000000000;
  s21_decimal res_od = s21_round(src1);
  s21_decimal result;
  result.bits[3] = 0b10000000000000000000000000000000;
  result.bits[2] = 0;
  result.bits[1] = 0b00000000000000000000001000010010;
  result.bits[0] = 0b00110110101101101000110001000000;
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_round_8) {
  s21_decimal src1;
  float a = -INFINITY;
  s21_from_float_to_decimal(a, &src1);
  s21_decimal res_od = s21_round(src1);
  ck_assert_float_eq(res_od.value_type, S21_NEGATIVE_INFINITY);
}
END_TEST

START_TEST(s21_truncate_1) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[3] = 0x000A0000;
  src1.bits[2] = 0x0;
  src1.bits[1] = 0xFFFFFFFF;
  src1.bits[0] = 0xFFFFFFFF;
  s21_decimal result;
  result.bits[3] = 0x0;
  result.bits[2] = 0x0;
  result.bits[1] = 0x0;
  result.bits[0] = 0x6DF37F67;
  s21_decimal res_od = s21_truncate(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_truncate_2) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[3] = 0x800C0000;
  src1.bits[2] = 0x0;
  src1.bits[1] = 0xFFFFFFFF;
  src1.bits[0] = 0xFFFFFFFF;
  s21_decimal result;
  result.bits[3] = 0x80000000;
  result.bits[2] = 0x0;
  result.bits[1] = 0x0;
  result.bits[0] = 0x1197998;
  s21_decimal res_od = s21_truncate(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_truncate_3) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[3] = 0x80000000;
  src1.bits[2] = 0x0;
  src1.bits[1] = 0xFFFFFFFF;
  src1.bits[0] = 0xFFFFFFFF;
  s21_decimal result;
  result.bits[3] = 0x80000000;
  result.bits[2] = 0x0;
  result.bits[1] = 0xFFFFFFFF;
  result.bits[0] = 0xFFFFFFFF;
  s21_decimal res_od = s21_truncate(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_truncate_4) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b00000000000000000000000001101101;
  src1.bits[1] = 0b00000000000011000110010101011011;
  src1.bits[2] = 0b00000000000000000011000000111001;
  src1.bits[3] = 0b00000000000011100000000000000000;
  s21_decimal result;
  result.bits[0] = 0b10000111101111000001011000011110;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal res_od = s21_truncate(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_truncate_5) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11011110101001001000000010110110;
  src1.bits[1] = 0b01011111101001011101111110100000;
  src1.bits[2] = 0b00011111111010011010111101100000;
  src1.bits[3] = 0b00000000000010010000000000000000;
  s21_decimal result;
  result.bits[0] = 0b00110100101011011100000100111110;
  result.bits[1] = 0b10001001000100001000011110111001;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal res_od = s21_truncate(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_truncate_6) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[3] = 0x80090000;
  src1.bits[2] = 0;
  src1.bits[1] = 0xFFFFEA34;
  src1.bits[0] = 0xFF837E4F;
  s21_decimal result = s21_truncate(src1);
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0x80000000;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0x4;
  result_origin.bits[0] = 0x4B829C70;
  ck_assert_int_eq(result_origin.bits[3], result.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result.bits[0]);
}
END_TEST

START_TEST(s21_truncate_7) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b11010000101000110011000001101101;
  src1.bits[1] = 0b00011111100110100110101101011000;
  src1.bits[2] = 0;
  src1.bits[3] = 0b00000000000010010000000000000000;
  s21_decimal result = s21_truncate(src1);
  s21_decimal result_origin = DEC_ZERO;
  result_origin.bits[3] = 0;
  result_origin.bits[2] = 0;
  result_origin.bits[1] = 0;
  result_origin.bits[0] = 0b10000111101111000001011000011110;
  ck_assert_int_eq(result_origin.bits[3], result.bits[3]);
  ck_assert_int_eq(result_origin.bits[2], result.bits[2]);
  ck_assert_int_eq(result_origin.bits[1], result.bits[1]);
  ck_assert_int_eq(result_origin.bits[0], result.bits[0]);
}
END_TEST

START_TEST(s21_truncate_8) {
  s21_decimal src1;
  src1.value_type = S21_NORMAL_VALUE;
  src1.bits[0] = 0b01111000101001111011110011000110;
  src1.bits[1] = 0b10011111111111001111101010000100;
  src1.bits[2] = 0b00011111111010011010111101101101;
  src1.bits[3] = 0b00000000000111000000000000000000;
  s21_decimal result;
  result.bits[0] = 0b00000000000000000000000000000000;
  result.bits[1] = 0b00000000000000000000000000000000;
  result.bits[2] = 0b00000000000000000000000000000000;
  result.bits[3] = 0b00000000000000000000000000000000;
  s21_decimal res_od = s21_truncate(src1);
  ck_assert_float_eq(res_od.bits[0], result.bits[0]);
  ck_assert_float_eq(res_od.bits[1], result.bits[1]);
  ck_assert_float_eq(res_od.bits[2], result.bits[2]);
  ck_assert_float_eq(res_od.bits[3], result.bits[3]);
}
END_TEST

START_TEST(s21_truncate_9) {
  s21_decimal src1;
  float a = INFINITY;
  s21_from_float_to_decimal(a, &src1);
  s21_decimal res_od = s21_truncate(src1);
  ck_assert_float_eq(res_od.value_type, S21_INFINITY);
}
END_TEST

START_TEST(s21_negate_random_test) {
  int i;
  s21_decimal number, res;
  for (i = 0; i <= RANDOM_TEST_COUNT; i++) {
    int num_i = random_int(1000000);
    int neg_num_i = random_int(1000000) * -1;
    float num_f = random_float();
    float neg_num_f = random_float() * -1;
    valToLog("s21_negate", num_i, 0);
    s21_from_int_to_decimal(num_i, &number);
    decToLog("function: s21_negate, num", number);
    res = s21_negate(number);
    decToLog("function: s21_negate, res", res);
    int sign = !!((1u << 31) & res.bits[S]);
    ck_assert_int_eq(sign, 1);
    writeLog("------------");
    valToLog("s21_negate", neg_num_i, 0);
    s21_from_int_to_decimal(neg_num_i, &number);
    decToLog("function: s21_negate, num", number);
    res = s21_negate(number);
    decToLog("function: s21_negate, res", res);
    sign = !!((1u << 31) & res.bits[S]);
    ck_assert_int_eq(sign, 0);
    writeLog("------------");
    valfToLog("s21_negate", num_f, 0);
    s21_from_float_to_decimal(num_f, &number);
    decToLog("function: s21_negate, num", number);
    res = s21_negate(number);
    decToLog("function: s21_negate, res", res);
    sign = !!((1u << 31) & res.bits[S]);
    ck_assert_int_eq(sign, 1);
    writeLog("------------");
    valfToLog("s21_negate", neg_num_f, 0);
    s21_from_float_to_decimal(neg_num_f, &number);
    decToLog("function: s21_negate, num", number);
    res = s21_negate(number);
    decToLog("function: s21_negate, res", res);
    sign = !!((1u << 31) & res.bits[S]);
    ck_assert_int_eq(sign, 0);
    writeLog("------------");
  }
  writeLog("----- next -----");
}
END_TEST

START_TEST(s21_negate_1) {
  int a = 10;
  int res_a = 0;
  s21_decimal src;
  s21_from_int_to_decimal(a, &src);
  s21_decimal res = s21_negate(src);
  s21_from_decimal_to_int(res, &res_a);
  ck_assert_int_eq(-10, res_a);
}
END_TEST

START_TEST(s21_negate_2) {
  float a = 10.12345;
  float res_a = 0;
  s21_decimal src;
  s21_from_float_to_decimal(a, &src);
  s21_decimal res = s21_negate(src);
  s21_from_decimal_to_float(res, &res_a);
  ck_assert_float_eq(-10.12345, res_a);
}
END_TEST

START_TEST(s21_negate_3) {
  float a = 10.1234e5;
  float res_a = 0;
  s21_decimal src;
  s21_from_float_to_decimal(a, &src);
  s21_decimal res = s21_negate(src);
  s21_from_decimal_to_float(res, &res_a);
  ck_assert_float_eq(-10.1234e5, res_a);
}
END_TEST

START_TEST(s21_negate_4) {
  s21_decimal tmp = DEC_MAX;
  tmp.value_type = S21_INFINITY;
  ck_assert_float_eq(S21_INFINITY, tmp.value_type);

  s21_long_decimal src;
  s21_copy_decimal_to_long_decimal(tmp, &src);
  set_long_sign(&src, !get_long_sign(src));
  ck_assert_float_eq(S21_NEGATIVE_INFINITY, src.value_type);

  s21_copy_long_decimal_to_decimal(src, &tmp);
  tmp = s21_abs(tmp);
  ck_assert_float_eq(S21_INFINITY, tmp.value_type);

  tmp = s21_negate(tmp);
  ck_assert_float_eq(S21_NEGATIVE_INFINITY, tmp.value_type);

  tmp = s21_negate(tmp);
  ck_assert_float_eq(S21_INFINITY, tmp.value_type);
}
END_TEST

int main() {
  // Random initialization
  srand(time(NULL));
  srand48(time(NULL));

  clearLog();

  Suite* s1 = suite_create("s21_decimal");
  TCase* s21_decCase = tcase_create("s21_decimal_comparativeTest");
  SRunner* sr = srunner_create(s1);
  int nf;

  tcase_set_timeout(s21_decCase, 90);
  suite_add_tcase(s1, s21_decCase);

  tcase_add_test(s21_decCase, s21_addition_random_test);
  tcase_add_test(s21_decCase, s21_addition_1);
  tcase_add_test(s21_decCase, s21_addition_2);
  tcase_add_test(s21_decCase, s21_addition_3);
  tcase_add_test(s21_decCase, s21_addition_4);
  tcase_add_test(s21_decCase, s21_addition_5);
  tcase_add_test(s21_decCase, s21_addition_6);
  tcase_add_test(s21_decCase, s21_addition_7);
  tcase_add_test(s21_decCase, s21_addition_8);
  tcase_add_test(s21_decCase, s21_addition_9);
  tcase_add_test(s21_decCase, s21_addition_10);
  tcase_add_test(s21_decCase, s21_addition_11);
  tcase_add_test(s21_decCase, s21_addition_12);
  tcase_add_test(s21_decCase, s21_addition_13);
  tcase_add_test(s21_decCase, s21_addition_14);
  tcase_add_test(s21_decCase, s21_addition_15);
  tcase_add_test(s21_decCase, s21_addition_16);
  tcase_add_test(s21_decCase, s21_addition_17);
  tcase_add_test(s21_decCase, s21_addition_18);
  tcase_add_test(s21_decCase, s21_addition_19);
  tcase_add_test(s21_decCase, s21_addition_20);
  tcase_add_test(s21_decCase, s21_addition_21);
  tcase_add_test(s21_decCase, s21_addition_22);

  tcase_add_test(s21_decCase, s21_substraction_random_test);
  tcase_add_test(s21_decCase, s21_substraction_1);
  tcase_add_test(s21_decCase, s21_substraction_2);
  tcase_add_test(s21_decCase, s21_substraction_3);
  tcase_add_test(s21_decCase, s21_substraction_4);
  tcase_add_test(s21_decCase, s21_substraction_5);
  tcase_add_test(s21_decCase, s21_substraction_6);
  tcase_add_test(s21_decCase, s21_substraction_7);
  tcase_add_test(s21_decCase, s21_substraction_8);
  tcase_add_test(s21_decCase, s21_substraction_9);
  tcase_add_test(s21_decCase, s21_substraction_10);
  tcase_add_test(s21_decCase, s21_substraction_11);
  tcase_add_test(s21_decCase, s21_substraction_12);
  tcase_add_test(s21_decCase, s21_substraction_13);
  tcase_add_test(s21_decCase, s21_substraction_14);
  tcase_add_test(s21_decCase, s21_substraction_15);
  tcase_add_test(s21_decCase, s21_substraction_16);
  tcase_add_test(s21_decCase, s21_substraction_17);

  tcase_add_test(s21_decCase, s21_multiply_random_test);
  tcase_add_test(s21_decCase, s21_multiply_1);
  tcase_add_test(s21_decCase, s21_multiply_2);
  tcase_add_test(s21_decCase, s21_multiply_3);
  tcase_add_test(s21_decCase, s21_multiply_4);
  tcase_add_test(s21_decCase, s21_multiply_5);
  tcase_add_test(s21_decCase, s21_multiply_6);
  tcase_add_test(s21_decCase, s21_multiply_7);
  tcase_add_test(s21_decCase, s21_multiply_8);
  tcase_add_test(s21_decCase, s21_multiply_9);
  tcase_add_test(s21_decCase, s21_multiply_10);
  tcase_add_test(s21_decCase, s21_multiply_11);
  tcase_add_test(s21_decCase, s21_multiply_12);
  tcase_add_test(s21_decCase, s21_multiply_13);
  tcase_add_test(s21_decCase, s21_multiply_14);
  tcase_add_test(s21_decCase, s21_multiply_15);
  tcase_add_test(s21_decCase, s21_multiply_16);
  tcase_add_test(s21_decCase, s21_multiply_17);
  tcase_add_test(s21_decCase, s21_multiply_18);
  tcase_add_test(s21_decCase, s21_multiply_19);
  tcase_add_test(s21_decCase, s21_multiply_20);
  tcase_add_test(s21_decCase, s21_multiply_21);
  tcase_add_test(s21_decCase, s21_multiply_22);
  tcase_add_test(s21_decCase, s21_multiply_23);

  tcase_add_test(s21_decCase, s21_division_random_test);
  tcase_add_test(s21_decCase, s21_division_1);
  tcase_add_test(s21_decCase, s21_division_2);
  tcase_add_test(s21_decCase, s21_division_3);
  tcase_add_test(s21_decCase, s21_division_4);
  tcase_add_test(s21_decCase, s21_division_5);
  tcase_add_test(s21_decCase, s21_division_6);
  tcase_add_test(s21_decCase, s21_division_7);
  tcase_add_test(s21_decCase, s21_division_8);
  tcase_add_test(s21_decCase, s21_division_9);
  tcase_add_test(s21_decCase, s21_division_10);
  tcase_add_test(s21_decCase, s21_division_11);
  tcase_add_test(s21_decCase, s21_division_12);
  tcase_add_test(s21_decCase, s21_division_13);
  tcase_add_test(s21_decCase, s21_division_14);
  tcase_add_test(s21_decCase, s21_division_15);
  tcase_add_test(s21_decCase, s21_division_16);
  tcase_add_test(s21_decCase, s21_division_17);
  tcase_add_test(s21_decCase, s21_division_18);
  tcase_add_test(s21_decCase, s21_division_19);
  tcase_add_test(s21_decCase, s21_division_20);
  tcase_add_test(s21_decCase, s21_division_21);

  tcase_add_test(s21_decCase, s21_mod_random_test);
  tcase_add_test(s21_decCase, s21_mod_1);
  tcase_add_test(s21_decCase, s21_mod_2);
  tcase_add_test(s21_decCase, s21_mod_3);
  tcase_add_test(s21_decCase, s21_mod_4);
  tcase_add_test(s21_decCase, s21_mod_5);
  tcase_add_test(s21_decCase, s21_mod_6);
  tcase_add_test(s21_decCase, s21_mod_7);
  tcase_add_test(s21_decCase, s21_mod_8);
  tcase_add_test(s21_decCase, s21_mod_9);
  tcase_add_test(s21_decCase, s21_mod_10);
  tcase_add_test(s21_decCase, s21_mod_11);

  tcase_add_test(s21_decCase, s21_is_less_random_test);
  tcase_add_test(s21_decCase, s21_is_less_test1);
  tcase_add_test(s21_decCase, s21_is_less_test2);
  tcase_add_test(s21_decCase, s21_is_less_test3);
  tcase_add_test(s21_decCase, s21_is_less_test4);
  tcase_add_test(s21_decCase, s21_is_less_test5);
  tcase_add_test(s21_decCase, s21_is_less_test6);
  tcase_add_test(s21_decCase, s21_is_less_test7);
  tcase_add_test(s21_decCase, s21_is_less_test8);


  tcase_add_test(s21_decCase, s21_is_less_or_equal_random_test);
  tcase_add_test(s21_decCase, s21_is_less_or_equal_test);

  tcase_add_test(s21_decCase, s21_is_greater_random_test);
  tcase_add_test(s21_decCase, s21_is_greater_test);

  tcase_add_test(s21_decCase, s21_is_greater_or_equal_random_test);
  tcase_add_test(s21_decCase, s21_is_greater_or_equal_test);

  tcase_add_test(s21_decCase, s21_is_equal_random_test);
  tcase_add_test(s21_decCase, s21_is_equal_test);

  tcase_add_test(s21_decCase, s21_is_not_equal_random_test);
  tcase_add_test(s21_decCase, s21_is_not_equal_test);

  tcase_add_test(s21_decCase, s21_from_int_to_decimal_random_test);
  tcase_add_test(s21_decCase, s21_from_int_to_decimal_test);

  tcase_add_test(s21_decCase, s21_from_float_to_decimal_random_test);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_1);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_2);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_3);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_4);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_5);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_6);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_7);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_8);
  tcase_add_test(s21_decCase, s21_from_float_to_decimal_9);

  tcase_add_test(s21_decCase, s21_from_decimal_to_int_random_test);
  tcase_add_test(s21_decCase, s21_from_decimal_to_int_1);
  tcase_add_test(s21_decCase, s21_from_decimal_to_int_2);
  tcase_add_test(s21_decCase, s21_from_decimal_to_int_3);
  tcase_add_test(s21_decCase, s21_from_decimal_to_int_4);
  tcase_add_test(s21_decCase, s21_from_decimal_to_int_5);
  tcase_add_test(s21_decCase, s21_from_decimal_to_int_6);

  tcase_add_test(s21_decCase, s21_from_decimal_to_float_random_test);
  tcase_add_test(s21_decCase, s21_from_decimal_to_float_1);
  tcase_add_test(s21_decCase, s21_from_decimal_to_float_2);
  tcase_add_test(s21_decCase, s21_from_decimal_to_float_3);
  tcase_add_test(s21_decCase, s21_from_decimal_to_float_4);
  tcase_add_test(s21_decCase, s21_from_decimal_to_float_5);

  tcase_add_test(s21_decCase, s21_floor_1);
  tcase_add_test(s21_decCase, s21_floor_2);
  tcase_add_test(s21_decCase, s21_floor_3);
  tcase_add_test(s21_decCase, s21_floor_4);
  tcase_add_test(s21_decCase, s21_floor_5);
  tcase_add_test(s21_decCase, s21_floor_6);
  tcase_add_test(s21_decCase, s21_floor_7);
  tcase_add_test(s21_decCase, s21_floor_8);

  tcase_add_test(s21_decCase, s21_round_1);
  tcase_add_test(s21_decCase, s21_round_2);
  tcase_add_test(s21_decCase, s21_round_3);
  tcase_add_test(s21_decCase, s21_round_4);
  tcase_add_test(s21_decCase, s21_round_5);
  tcase_add_test(s21_decCase, s21_round_6);
  tcase_add_test(s21_decCase, s21_round_7);
  tcase_add_test(s21_decCase, s21_round_8);

  tcase_add_test(s21_decCase, s21_truncate_1);
  tcase_add_test(s21_decCase, s21_truncate_2);
  tcase_add_test(s21_decCase, s21_truncate_3);
  tcase_add_test(s21_decCase, s21_truncate_4);
  tcase_add_test(s21_decCase, s21_truncate_5);
  tcase_add_test(s21_decCase, s21_truncate_6);
  tcase_add_test(s21_decCase, s21_truncate_7);
  tcase_add_test(s21_decCase, s21_truncate_8);
  tcase_add_test(s21_decCase, s21_truncate_9);

  tcase_add_test(s21_decCase, s21_negate_random_test);
  tcase_add_test(s21_decCase, s21_negate_1);
  tcase_add_test(s21_decCase, s21_negate_2);
  tcase_add_test(s21_decCase, s21_negate_3);
  tcase_add_test(s21_decCase, s21_negate_4);

  srunner_run_all(sr, CK_ENV);
  nf = srunner_ntests_failed(sr);
  srunner_free(sr);

  return nf == 0 ? 0 : 1;
}
