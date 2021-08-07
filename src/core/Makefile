
FSTAR=fstar.exe --cache_dir "../checked_cache"

all: ../checked_cache/AMem.ADom.fst.checked

.depends:
	$(FSTAR) --dep full AMem.ADom.fst 2>/dev/null > .depends
include .depends

../checked_cache/%.checked:
	$(FSTAR) --cache_checked_modules "$*"

