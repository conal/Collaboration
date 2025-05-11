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

If you're familiar with my work or you've listened to the interviews linked above, you'll know that I prefer denotational to operational perspectives.
I am eager, however, to compare the two styles honestly and substantively; so I'm quite interested in side-by-side comparisons on that dimension as well, with shared specification and evaluation criteria.

For mentoring, a typical getting started path looks something like the following:

*   Install Agda.
*   Read some of the Agda resources I recommended, and work through the exercises you find.
    You may ask me questions along the way.
*   Send me a progress update every two weeks (preferably in Markdown format without section headings), even if it's short, so I know that you're still in the game.
*   When I see that you're getting some basic Agda skills down, I will start feeding you exercises from the book I am writing.
*   When you get the hang of compositionally correct computing, we can start digging into topics of particular interest to you, aiming at doing and sharing some original research.

You can find my email address near the bottom of my [home page](http://conal.net).
