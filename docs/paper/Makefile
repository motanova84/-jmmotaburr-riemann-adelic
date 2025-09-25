# Makefile for LaTeX document compilation

# Main document name (without .tex extension)
MAIN = main

# LaTeX compiler
LATEX = pdflatex

# Output directory
OUTDIR = .

.PHONY: all clean

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex sections/*.tex ../teoremas_basicos/*.tex
	$(LATEX) -output-directory=$(OUTDIR) $(MAIN).tex
	$(LATEX) -output-directory=$(OUTDIR) $(MAIN).tex

clean:
	rm -f *.aux *.log *.out *.toc *.pdf

help:
	@echo "Available targets:"
	@echo "  all    - Build the PDF document"
	@echo "  clean  - Remove generated files"
	@echo "  help   - Show this help message"