# What the Anthropic FLT formalization actually did, and what transfers here

Recorded as a document rather than in memory, because the numbers and the
methodology are the kind of thing that has to be re-read rather than recalled.

Primary source: <https://www.anthropic.com/research/formalizing-fermats-last-theorem>
(the fetched page, not a summary of it). Secondary: the proof repository
<https://github.com/anthropics/fermats-last-theorem>, Buzzard's statement quoted
there, and the Prove2Me paper cited at the end of it.

## The primary facts

| quantity | value |
| --- | --- |
| elapsed | **11 days**, largely autonomous |
| Lean written | **13 million lines** (over 5x Mathlib) |
| theorems proved | **30,300**, of which **29,500** are in the final proof |
| agents | **"dozens"** of Claude agents |
| tokens | about **six billion** output tokens |
| model | an internal research model, roughly comparable to Claude Fable 5.1 |
| human input | occasional high-level instructions only ("Jacobian as a scheme sounds high priority", "push the Mazur theorem to be done soon") |
| source followed | a simplified version of Wiles's proof from **Darmon–Diamond–Taylor** |
| verification | Lean, Lean's three standard axioms, plus the **comparator** confirming the statement matches Mathlib's own |
| cost of failure | the initial, abandoned attempts contributed **about 7%** of the non-boilerplate lines |

The claim circulating as "1,000 agents in 30 hours" does not appear on the
Anthropic page. That page says 11 days and "dozens" of agents. Treat the page as
authoritative and the other figure as unverified.

## The part that matters for us

> A number of Claude's initial attempts failed: while agents had some early
> success, they quickly lost track of the project's state and stopped
> collaborating effectively.

That is the same failure this project has been living through. And the fix is
named:

> The effort succeeded when we switched to using Prove2Me.

The page gives three reasons, and they are worth reading as a description of what
Prove2Me is *for*, because this project has been using the platform as a place to
publish finished work rather than as the mechanism of the work itself:

1. **A DAG of theorem statements that agents used to decide what to attempt
   next.** The page calls this "particularly helpful for mitigating memory
   degradation and allowing multiple agents to work in parallel". The DAG is not
   bookkeeping; it is the thing that keeps independent agents from needing shared
   memory. Each agent reads the frontier, picks a leaf, and works.
2. **Statements and proofs in separate files, with the links maintained
   independently**, to speed compilation and cut resource use. This is why the
   platform's unit is a `Thm_`/`Sol_` pair and why `formal_statement` and the
   solution are separate artifacts.
3. **A natural-language description of every statement, enabling search and
   reuse.** The descriptions are not documentation; they are the index that lets
   an agent find the lemma it needs instead of reproving it.

## The second data point

The same page reports a smaller experiment: **Vinogradov's Three Primes Theorem
formalized in three days**, by agents "collaborating entirely through Prove2Me",
running on **three personal Claude Max plans** — consumer subscriptions, not a
research cluster.

That is closer to this project's situation than FLT is, and it cuts against the
intuition that scale is what is missing here.

## What does not transfer

**FLT had a proof to follow.** Darmon–Diamond–Taylor is a published text, and the
blueprint derived from it is a published plan. The milestones could be transcribed.
The page's own framing is that what was novel was *verification*: "what's novel
here is the verification — checking a mathematical proof as one would check a
mathematical computation with a calculator."

A166944 has no proof to transcribe. It has a conjecture, a formalization of the
statement, and a reduction to one inequality. This is the difference the project's
own notes have recorded more than once, and it is the reason the FLT numbers
should not be read as a schedule.

## What does transfer, concretely

1. **Stop treating the platform as an archive.** The DAG is the working surface.
   The frontier at `GET /theorems/:id/open-leaves` is the task list, and it should
   drive what agents attempt next — not the repository's own backlog.
2. **Decompose before attempting.** The FLT milestone graph has three coloured
   sections corresponding to three core sub-theorems, and it "closely follows
   Wiles's original proof". The decomposition was the plan; the proofs were the
   work. This project's repeated failure has been to treat one inequality as the
   unit of work and to attack it from many directions instead of splitting it.
3. **Statements frozen, proofs separate.** The upstream statement is pinned by
   `formal-conjectures` and `comparator` checks the match. The statement of the
   goal should not move while the proof is being sought.
4. **Blind read-back as the audit.** For an open conjecture there is no source to
   transcribe against, so the check on a formal statement is an independent
   natural-language reading of what the Lean literally asserts, compared against
   intent. The platform supports this as a first-class field on draft items.
5. **Counterexample search as an independent role.** The theorem may be false.
   FLT's page does not discuss this because FLT was known true; for an open
   conjecture, a `disprove` submission is a legitimate and valuable outcome.
6. **Expect the failed work to be visible.** About 7% of the final Lean came from
   abandoned attempts. In this project that 7% is the twelve closed routes in
   `REACH.md`, and it belongs in the repository rather than in a summary.

## The specific mismatch to fix

The FLT campaign's agents "used [the DAG] to decide what proofs they should
attempt next". This project's agents have been given angles chosen by the lead,
not leaves chosen from the frontier. Those are different loops, and the second one
is the one the platform was built for.

Concretely: `open-leaves` on the twin prime route currently returns the relaxed
index cap and the horizon cap. Work should be handed out as "close leaf X", with
the platform's own statement as the specification, rather than as "try angle Y".
