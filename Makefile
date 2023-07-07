.PHONY: check html-render

check:
	agda --safe --without-K chad-cost.agda

html-render:
	agda --html --safe spec.agda
	sed -n '/elided in the paper appendix/ { p; : loop; n; /^<\/pre>/ b rest; b loop; }; : rest; p' html/spec.LACM.html >html/spec.LACM.trimmed.html
