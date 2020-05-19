
ENCODINGS = FinLabels LinearLogic LabelDependent

all: $(ENCODINGS:%=SessionTypes/%/Proofs.agdai)

%.agdai: %.agda
	agda $<

clean:
	rm `find . -name "*.agdai"`
