CC = gcc
CFLAGS = -c -Wall -Wextra -Werror -std=c11
LDFLAGS = -Wall -Wextra -Werror -std=c11
OS := $(shell uname -s)

ifeq ($(OS), Darwin)
	OPEN_CMD = open
	PATH := $(PATH):$(HOME)/homebrew/bin:$(HOME)/.brew/bin
endif
ifeq ($(OS),Linux)
	OPEN_CMD = xdg-open
	PATH := $(PATH)
	ADD_LIB = -lm -lrt -pthread -D_GNU_SOURCE
endif

GCOV = --coverage

all: check s21_decimal.a test

s21_decimal.a: s21_decimal.c s21_decimal.h
	$(CC) $(CFLAGS) s21_decimal.c
	ar rcs $@ s21_decimal.o

test: test_s21_decimal.c test_s21_decimal.h s21_decimal.a
	${CC} ${LDFLAGS} -o $@ test_s21_decimal.c s21_decimal.a -lcheck $(ADD_LIB)
	./$@

gcov_report: clean lcov s21_decimal.c test_s21_decimal.c test_s21_decimal.h
	-mkdir report
	$(CC) $(CFLAGS) $(GCOV) s21_decimal.c test_s21_decimal.c $(ADD_LIB)
	$(CC) -o $@ $(LFLAGS) $(GCOV) s21_decimal.o test_s21_decimal.o -lcheck $(ADD_LIB)
	-./$@
	gcov test_s21_decimal.c
	$(shell PATH=$(PATH) which lcov) -t s21_decimal -o s21_decimal.info -c -d . --no-external
	$(shell PATH=$(PATH) which genhtml) -o report s21_decimal.info
	$(OPEN_CMD) ./report/index.html 

check: $(SOURCE) $(HEADER)
ifeq ("","$(wildcard ./CPPLINT.cfg)")
	cp -f ../materials/linters/CPPLINT.cfg ./CPPLINT.cfg
endif
	-python ../materials/linters/cpplint.py --extensions=c s21_decimal.c
	-python ../materials/linters/cpplint.py --extensions=c test_s21_decimal.c
	-cppcheck --enable=all --suppress=missingIncludeSystem --suppress=unusedFunction s21_decimal.c test_s21_decimal.c

lcov:
ifeq ("", "$(shell PATH=$(PATH) which lcov)")
	$(error Need to install lcov)
endif
	
clean: 
	-rm -rf *.o && rm -rf *.gcno
	-rm -rf *.a && rm -rf *.gcda
	-rm -rf *.info && rm -rf *.gcov
	-rm -rf ./test && rm -rf ./gcov_report
	-rm -rf ./report/ && rm -f *.log

rebuild: clean all

.PHONY: all clean rebuild check lcov
