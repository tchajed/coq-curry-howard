default: CurryHoward.html

CurryHoward.vo: CurryHoward.v
	coqc -noinit $<

CurryHoward.html: CurryHoward.vo
	coqdoc --parse-comments CurryHoward.v
