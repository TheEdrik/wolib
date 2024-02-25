INCDIRS := -I/home/tvi/warez/now/code.tmp
HEADERS := $(wildcard *.h)
SRC     := $(wildcard *.c)

sat: sat.c $(HEADERS)
	$(CC) -Wall -Wextra $(INCDIRS) -o $@ sat.c -lhiredis -lm

TIDY     :=
CLEAN    := sat.o sat tags cscope.out

##-------------------------------------
cscope: cscope.out

cscope.out: $(HEADERS) $(SRC)
	cscope -v -c -b $(sort $^)

tags: $(HEADERS) $(SRC)
	ctags --language-force=c $(sort $^)

##-------------------------------------
tidy:
	$(if $(wildcard $(TIDY)),$(RM) $(wildcard $(TIDY)))

clean: tidy
	$(if $(wildcard $(CLEAN)),$(RM) $(wildcard $(CLEAN)))

.PHONY:  clean tidy

