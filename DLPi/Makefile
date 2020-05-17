
SOURCES = $(wildcard *.agda)

all:
	agda Main.agda

update-license:
	@for i in *.agda; do \
		TMP=`mktemp`; \
		tail -n +16 $$i >$$TMP; \
		cat ../LICENSE.agda >$$i; \
		cat $$TMP >>$$i; \
	done

.PHONY: clean
clean:
	rm -f *.agdai
