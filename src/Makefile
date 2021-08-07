
FSTAR=fstar.exe --include core --include app --include app/PrettyPrinter --include app/StarCombinator --cache_dir "checked_cache"

all: checked_cache/Main.fst.checked

.depends:
	$(FSTAR) --dep full Main.fst 2>/dev/null > .depends
include .depends

checked_cache/%.checked:
	$(FSTAR) --cache_checked_modules "$*"

