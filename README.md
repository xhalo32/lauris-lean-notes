# Notes on Lean

Source files for [Notes on Lean](https://www.mv.helsinki.fi/home/lsoksane/lean/). Lean files in `Notes/` are translated into [Verso](https://github.com/leanprover/verso) documents, and `Document.md` gathers them into a single document. 

The Lean files must 

* alternate between code and block comments
* have block comment delimiters on lines of their own 
* have maximum length of 60 for code lines 
* use Verso's syntax in block comments
* have the following header
```
/-
[Title]
%%%
tag := "sec-[label]"
%%%
-/
[imports]
/-
```

[Fish shell](https://fishshell.com/) script `scripts/generate.fish` does the translation, calls Verso to compile the document, and postprocesses the resulting HTML. It relies on [jq](https://jqlang.org/) together with some Python libraries (see `scripts/postprocess.py`). 

To inspect the generated site locally, run e.g.
```
python -m http.server 8000
```
in `_out/_out/html-multi`, and open [localhost:8000](http://localhost:8000/).


## Configuration

The Verso translation is generated in `_out/`. This can be overridden by setting `outdir` in `_local/config.fish`. When local configuration in used, `_local/` should be put in `.git/info/exclude`. It is also useful to have `.vscode/` there, and have

```
  "editor.rulers": [60],
```
in `.vscode/settings.json`.