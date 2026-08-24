# Build the Alectryon PDF of the LeemFO proofs.
#
# Default driver is `noop`: LeanInk (Alectryon's Lean 4 executor) is
# archived on Lean 4.6 and does not speak Lean 4.33. The literate
# source still typechecks with `lake build LeemFOProofs`.
# If a matching `leanInk` is on PATH, run `make DRIVER=leanInk`.

ROOT        := $(abspath ../..)
VENV        := $(ROOT)/.venv
ALECTRYON   := $(VENV)/bin/alectryon
SRC         := LeemFOProofs.lean
TEX         := leemfo_alectryon.lua.tex
PDF         := leemfo_alectryon.pdf
DRIVER      ?= noop
LATEX_DIAL  ?= lualatex
CACHE       := .alectryon-cache
LAKE_FLAG   := $(if $(filter leanInk,$(DRIVER)),--lake $(ROOT)/lakefile.toml,)

.PHONY: all venv tex pdf clean

all: pdf

venv: $(ALECTRYON)

$(ALECTRYON):
	uv venv $(VENV)
	uv pip install --python $(VENV)/bin/python -r $(ROOT)/docs/alectryon/requirements.txt

tex: venv $(SRC) docutils.conf
	$(ALECTRYON) \
	  --frontend lean4+rst \
	  --backend latex \
	  --latex-dialect $(LATEX_DIAL) \
	  --lean4-driver $(DRIVER) \
	  --copy-assets copy \
	  --long-line-threshold 0 \
	  --cache-directory $(CACHE) \
	  $(LAKE_FLAG) \
	  $(SRC) -o $(TEX)

pdf: tex
	latexmk -$(LATEX_DIAL) -interaction=nonstopmode -halt-on-error $(TEX)
	@test -f leemfo_alectryon.lua.pdf
	mv -f leemfo_alectryon.lua.pdf $(PDF)

clean:
	latexmk -C -$(LATEX_DIAL) $(TEX) >/dev/null 2>&1 || true
	rm -f $(TEX) $(PDF) \
	  leemfo_alectryon.lua.aux leemfo_alectryon.lua.log \
	  leemfo_alectryon.lua.out leemfo_alectryon.lua.toc \
	  leemfo_alectryon.lua.fls leemfo_alectryon.lua.fdb_latexmk \
	  leemfo_alectryon.lua.synctex.gz
	rm -rf $(CACHE)
