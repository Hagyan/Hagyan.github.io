# Adding the LaTeX packages

The public page is `latex.html`. It reuses `style.css` and is linked from the main site navigation. This is a placeholder, not a software release.

## Where files go

| Material | Folder / suggested filename |
|---|---|
| Symbol-renaming package | `latex/symbols/` (keep your actual .sty filename) |
| Formatting package | `latex/formatting/` |
| Graphics package | `latex/graphics/` |
| Complete compiled guide | `latex/docs/quick-start.pdf` |
| First few pages only | `latex/docs/quick-start-preview.pdf` |
| Compiled cheat sheet | `latex/docs/cheat-sheet.pdf` |
| Documentation source | `latex/docs/` (.tex and required assets) |
| Minimal examples | `latex/examples/` |

The three folder names are organizational labels, not finalized package names. Do not rename a .sty file without updating its package declaration and examples.

## Upload without a terminal

1. Open this repository on GitHub and navigate into the desired folder under `latex/`.
2. Choose **Add file → Upload files** and select the finished files from your computer.
3. Review filenames and content. Do not upload private homework, credentials, private comments, or unrelated materials.
4. Enter a short message such as “Add symbol-renaming package draft”.
5. Commit to `main` when ready to make the files public. A separate branch is useful if you want to review changes before publishing.
6. Repeat for the other packages and documentation. Each folder already contains a README.
7. Update each folder README with the actual filenames, dependencies, installation instructions, and a working example.

## Activate the website links

Edit `latex.html` using its pencil button on GitHub. Replace the appropriate “forthcoming” message with a real link only after uploading the file. For example:

```html
<a href="https://github.com/Hagyan/Hagyan.github.io/tree/main/latex/symbols">Source and examples</a>
<a href="latex/docs/quick-start.pdf">Download the complete guide (PDF)</a>
<a href="latex/docs/cheat-sheet.pdf">Download the cheat sheet (PDF)</a>
```

Use the real .sty filename for an individual file download link.

For the inline preview, export only the first few pages as `quick-start-preview.pdf`. Merely opening a complete PDF at page 1 does not restrict it to its first pages. In `latex.html`, replace the preview placeholder with the commented-out object and fallback-link markup, removing the surrounding HTML comment markers. The ordinary PDF link remains usable on phones or browsers without an inline viewer.

Change the status and descriptions to match what is actually available; leave unfinished components marked forthcoming. Commit the edits, then check the live page and each link after the Pages deployment completes. Use the repository’s Actions tab if a deployment fails.

## What “commit” means

A commit is a named snapshot of changes, not a promise that your project is finished and not an academic publication or formal release. Small draft commits are normal. Git history lets you inspect earlier versions and undo ordinary edits with another commit.

This repository is already public. Files committed here are publicly accessible; changes to the published branch can also update the website. Removing a file in a later commit does not necessarily remove it from history or copies others have made.

A release is a separate optional milestone, often tagged with a version such as v0.1.0. You can later make a release ZIP containing just the package suite and documentation; the website repository’s default “Download ZIP” includes the entire website and research archive, so it is not a package-only download.

## Before calling a package ready

- Compile a minimal example for each package in the intended TeX engine and on Overleaf.
- Document dependencies, engine requirements, command conflicts, and package version.
- Ensure the cheat sheet matches the released commands.
- Include only material you have the right to distribute; choose an appropriate license before encouraging reuse. No license is selected by this placeholder.
- If the suite gets its own repository, change the GitHub links in `latex.html` to that repository. No separate repository is created by this website update.
