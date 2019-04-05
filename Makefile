# Fill this in with the path to the `hoqc` command, if not installed globally.
PATH_TO_HOQ=

HOQC=$(PATH_TO_HOQ)hoqc

all: Groupoid.vo GroupoidQuotient.vo

Groupoid.vo:
	$(HOQC) Groupoid.v

GroupoidQuotient.vo: Groupoid.vo
	$(HOQC) GroupoidQuotient.v

clean:
	rm *.vo *.glob
