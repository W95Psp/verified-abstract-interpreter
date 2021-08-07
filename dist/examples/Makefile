ANALYSER_BINARY := "/nix/store/s2kr08qshjg8zvlsnad8jzr9vj6yqqm4-AbIntFStar/bin/analyser"
ifdef ANALYSER_BINARY
RUNNER := $(ANALYSER_BINARY)
else
RUNNER := $(shell nix build --no-link ..#analyser && nix path-info ..#analyser)/analyser
endif

TESTS := $(patsubst %.c, %, $(wildcard *.c))

%: %.c
	@echo -e "\n\x1b[43m\x1b[1m  Test \`$^\`  \x1b[0m"
	@($(RUNNER) $(realpath $^) || (echo -e '\n' && false)) && (echo -e "\n  \x1b[42m\x1b[1mOk\x1b[0m")

all: $(TESTS)

clean:
	rm -f *.success

.PHONY: all clean
