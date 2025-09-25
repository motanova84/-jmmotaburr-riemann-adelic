# Makefile for building the RH paper

.PHONY: all clean distclean

# Default target
all: main.pdf

# Main paper compilation
main.pdf: main.tex sections/*.tex
	@echo "Compiling RH paper..."
	pdflatex main.tex
	pdflatex main.tex
	@echo "Paper compilation complete: main.pdf"

# Quick build (single pass)
quick: main.tex sections/*.tex
	pdflatex main.tex

# Alternative build using latexmk
latexmk: main.tex sections/*.tex
	latexmk -pdf main.tex

# Clean auxiliary files
clean:
	rm -f *.aux *.log *.out *.toc *.fls *.fdb_latexmk *.synctex.gz

# Complete clean including PDF
distclean: clean
	rm -f main.pdf

# Help target
help:
	@echo "Available targets:"
	@echo "  all       - Build the complete paper (default)"
	@echo "  quick     - Quick build (single LaTeX pass)"
	@echo "  latexmk   - Build using latexmk"
	@echo "  clean     - Remove auxiliary files"
	@echo "  distclean - Remove all generated files including PDF"
	@echo "  help      - Show this help message"