*Would you like to play/learn/work with me?*

I am seeking research collaborators and mentees in the general area of correct and efficient engineering with *simple* and precise specifications.
To keep us honest, we'd formalize our questions and answers in one or more proof assistants (my favorite being Agda), eliminating guesswork, subjectivity, and false assumptions.
(As Richard Feynman put it, "The first principle is that you must not fool yourself, and you are the easiest person to fool."
Bertrand Russell made the point even more specifically: "Everything is vague to a degree you do not realize till you have tried to make it precise.")

With this commitment to (and support for) truth in place, we would then look for the simplest (and thus most valuable) possible specifications for problems of interest.
(Simplicity of specifications is important not only for ease of use but also crucial to reliability, since the specification/question is the one aspect of the work that cannot be formally verified.)
With such a specification, we would look for efficient implementations and tractable (and thus affordable) proofs (demonstrations of correctness).

I personally believe these values are necessary for doing work of lasting scientific value (as opposed to merely short-term commercial value) and for moving our technological society off its rickety foundations onto solid ground.

I discussed my values and why they matter to me in three interviews:

*   [The Lost Elegance of Computation](https://www.typetheoryforall.com/episodes/the-lost-elegance-of-computation) (3:32)
*   [Denotational Design](https://www.typetheoryforall.com/episodes/denotational-design) (3:07)
*   [Haskell Interlude](https://haskell.foundation/podcast/62/) (0:58)

See also my ZuriHac 2023 talk, [A Galilean revolution for computing:
Unboundedly scalable reliability and efficiency](https://github.com/conal/talk-2023-galilean-revolution) (1:27).

It took some experience mentoring people to realize the importance of asking them to work with a proof assistant.
Before that (working in Haskell), I found myself repeatedly reminding mentees of the success/correctness criteria, and I didn't enjoy the role.
Eventually it dawned on me that dependent types could capture these criteria precisely and remind the mentees whenever they strayed.
A modern dependently typed language seems the best foundation for proof assistants, thanks to embodying the profound Curry-Howard-Lambek correspondence.
Agda is my favorite dependently typed language / proof assistant, so it's where I now do all of my work, including generation of efficient parallel computational hardware with formal correctness proofs (and simple specifications).
To help you get started, I've collected some suggestions about [Learning Agda](learning-agda.md).
I'm also open to using other proof assistants *in combination with* Agda for the sake of comparison.

For mentoring, a typical getting started path looks something like the following:

*   Install Agda.
*   Read some of the Agda resources I recommended, and work through the exercises you find.
    You may ask me questions along the way.
*   Send me a progress update every two weeks (preferably in Markdown format without section headings), even if it's short, so I know that you're still in the game.
    Between progress updates, you're welcome to write to me as often as you like with questions etc.
    It helps my journal-centered workflow if we both write in [Markdown](https://en.wikipedia.org/wiki/Markdown) format with pretty links, without section headings, and with blank lines before lists and enumerations.
    Also, "agda" in the fenced code header, and single back-ticks around in-line code.
*   Assemble a list of topics that interest you, and start investigating, emphasizing simple and precise specifications.
    (A topic can even start with some code you've read or written.)
    I'll ask clarifying questions and make a few suggestions (hopefully not too intrusively), and we'll iterate from there.
*   If anything in the process isn't working for you, please say so, and we'll adapt to suit us both.
    If you want to quit, that's fine, but I prefer hearing so explicitly.

You can find my email address near the bottom of my [home page](http://conal.net).

## Setting up an Agda environment with Nix

This repository provides a Nix flake that supplies Agda with the [standard library](https://github.com/agda/agda-stdlib) and [Felix](https://github.com/conal/felix) (Conal's categorical denotational design library) pre-compiled.
The only prerequisite is [Nix](https://nixos.org/download/) with flakes enabled.

### 1. Install Nix (if you don't have it)

The recommended installer is [Determinate Nix](https://determinate.systems/nix-installer/), which already has flakes enabled — no extra configuration needed:

```bash
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
```

### 2. Enter the development shell

From the repository root:

```bash
nix develop
```

This drops you into a shell with `agda` and `agda-mode` on your `PATH`, the standard library available, and [Felix](https://github.com/conal/felix) (Conal's Agda library for categorical denotational design) pre-compiled.
You can now type-check or compile any Agda file in the repository, and `import Felix.*` works without any extra flags.

### 3. Using direnv (recommended)

[direnv](https://direnv.net/) activates the Nix devShell automatically when you `cd` into the project, so you don't have to run `nix develop` manually each time.

Install direnv, then allow the project's `.envrc`:

```bash
direnv allow
```

From now on, entering the project directory will automatically load the Agda environment.

## Setting up Emacs / Spacemacs for Agda

Interactive Agda editing in Emacs/Spacemacs relies on three pieces:

1. **direnv** activates the project's Nix devShell automatically when a file in the repo is opened.
2. The devShell provides the wrapped `agda` binary (with Felix pre-compiled) and the `agda-mode` binary.
3. A hook in your Emacs config defers to the devShell's `agda-mode` instead of any globally-installed one.

### Prerequisites

*   `direnv` installed and its Emacs integration active (`direnv-mode` or the `envrc` package).
*   No separate global `agda` or `agda-mode` install is required — everything comes from the Nix devShell.

### Spacemacs snippet

Add the following inside `dotspacemacs/user-config` in your `~/.spacemacs`:

```elisp
(defun my/maybe-activate-agda-mode ()
  "Activate agda2-mode for Agda files using the project's direnv environment.
Deferred via idle-timer. Derives the agda2.el path directly from the
agda-mode binary path to avoid shell-command-to-string timing issues."
  (when (and (buffer-file-name)
             (string-match-p "\\.l?agda\\(?:\\.md\\)?\\'" (buffer-file-name))
             (not (eq major-mode 'agda2-mode)))
    (let ((buf (current-buffer)))
      (run-with-idle-timer
       0 nil
       (lambda ()
         (when (buffer-live-p buf)
           (with-current-buffer buf
             (ignore-errors (direnv-update-directory-environment default-directory))
             (when (not (eq major-mode 'agda2-mode))
               (let* ((agda-mode-bin (executable-find "agda-mode"))
                      (agda2-el (when agda-mode-bin
                                  (car (last
                                        (seq-filter
                                         (lambda (l) (string-suffix-p ".el" l))
                                         (split-string
                                          (shell-command-to-string
                                           (concat agda-mode-bin " locate"))
                                          "\n" t)))))))
                 (if (and agda2-el (file-exists-p agda2-el))
                     (progn
                       (add-to-list 'load-path (file-name-directory agda2-el))
                       (unless (featurep 'agda2-mode)
                         (load-file agda2-el))
                       (agda2-mode))
                   (message "agda2-mode: locate failed (bin=%s locate=%s)"
                            agda-mode-bin agda2-el)))))))))))

(add-hook 'find-file-hook #'my/maybe-activate-agda-mode)
```

Once this is in place, opening any `.agda` file in the repository will automatically activate `agda2-mode` with the correct environment.
You can then load and type-check the file with `C-c C-l`.

## Running the limited-recursion example

The `limited-recursion/` directory contains `telomare.agda`, a denotational specification of Telomare's semantics following Conal's Denotational Design methodology.
See [limited-recursion/README.md](limited-recursion/README.md) for a detailed explanation.

### Compile and run from the devShell

```bash
nix develop            # or let direnv do it
agda --compile limited-recursion/telomare.agda
./limited-recursion/telomare
```

### Build and run with Nix directly (no devShell needed)

```bash
nix run                # builds and runs the limited-recursion example
```

### Run the checks

```bash
nix flake check        # verifies fibonacci output matches expected
```
