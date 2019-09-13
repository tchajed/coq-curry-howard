COQDOCFLAGS:= \
	--html \
	--no-lib-name --parse-comments \
	--with-header extra/header.html --with-footer extra/footer.html

default: doc/CurryHoward.html

CurryHoward.vo: CurryHoward.v
	@echo "COQC -noinit"
	@coqc -noinit $<

doc/CurryHoward.html: CurryHoward.vo
	@echo "COQDOC"
	@coqdoc $(COQDOCFLAGS) -d doc CurryHoward.v

clean:
	@echo "CLEAN"
	@rm -f *.vo *.glob .*.aux
	@rm -f doc/*.html doc/coqdoc.css

.PHONY: clean
