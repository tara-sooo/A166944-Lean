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

**Correction, and an earlier error of mine.** I first recorded here that the
"1,000 agents in 30 hours" figure "does not appear on the Anthropic page", on the
strength of the September page alone. That was wrong: it is a **second, separate
result**, published on 2026-11-09 with Fable 5.2 / Mythos 5.2. Both figures are
Anthropic's. See the next section. The lesson is the one this project keeps
relearning, applied to sources rather than to arithmetic: a search that stops at
the first confirming hit is not a check.

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


## The second run: 1,000 agents, 28.7 hours, and no platform

Source: <https://claude.dev/blog/safely-scaling-multi-agent-teams-with-fable-5-2/>
(Barry Zhang, Tianyi Peng, Elle Najt, Keller Scholl, Lance Martin; 2026-11-09), with
the release announcement at <https://www.anthropic.com/claude-fable-and-mythos-5-2>.

This is a **reproduction**, not a fresh proof: the agents were handed a list of 60
statements, a one-sentence sketch of the classical route, the definitions those
statements use, and 47 proved lemmas from the September run. They were told to write
Lean proofs, build and check them, and submit to a shared main branch where a grader
checked them.

| | September (Prove2Me) | November (SQL) |
| --- | --- | --- |
| elapsed | 11 days | **28.7 hours** |
| agents | dozens | **1,000** (1 lead + 999 helpers) |
| output tokens | ~6 billion | **one third as many** |
| proof length | 13 million lines | **one seventh** |
| scaffolding | Prove2Me's DAG + a researcher steering | 60 statements, 47 lemmas, one-sentence sketch |
| coordination | provided by the platform | **the agents built it themselves** |
| human steering | occasional instructions | none during the run |

### What replaced Prove2Me

A **shared Postgres database**, chosen because "its transactions handle concurrent
writes from 1,000 agents, and Claude is already familiar with it". The lead created
five tables **in the first ten minutes**:

| table | purpose |
| --- | --- |
| `Announce` | the lead's orders to everyone |
| `Assign` | who owns which statement |
| `Notes` | an open board for claiming work and reporting progress |
| `Subtasks` | a to-do list; anyone may add, first claimer owns |
| `Landed` | a log of finished work |

Then it assigned each statement to a crew of 16–17 helpers (999 rows), made one
helper per crew a **captain** responsible for posting a plan and splitting work, and
told every helper to begin by **judging its statement's difficulty**.

### The lead's actual job, which is the transferable part

It was not proving anything. It was three things:

1. **Triage by difficulty.** About 27 minutes in, with three statements proved, the
   lead read the posted verdicts and set aside the 47 that most helpers judged
   infeasible in budget, reassigning nearly everyone to the remaining 10. All ten
   were proved within about 70 minutes, and the lead's own comment is the point:
   *"the team's throughput is far higher than the early 'infeasible-in-budget'
   verdicts assumed"*.
2. **Reassignment.** *"there is no reason to idle"* -- helpers were moved to harder
   statements as the easy ones landed. By hour 3 the lead told free helpers *"do not
   wait for me"*, so they could pick up work without waiting for an assignment.
3. **Splitting the one hard statement as a tree.** With only Langlands–Tunnell left,
   whose own captain had estimated 0.7–1 million lines and *under a 1% chance* of
   finishing, the lead moved ~750 helpers onto it with the words *"Honest odds are
   low."* The work became a **tree of 2,418 tasks, up to 10 levels deep**, growing
   whenever a piece was too big for one helper.

The structural trick in that tree is stated plainly and is the single most useful
sentence in the post for this project:

> Each piece could assume the pieces beneath it, so hundreds of helpers could work
> in parallel before those pieces were proved.

### Anthropic's own conclusions, which bear directly on how this project is run

> Agents tend to give up on hard problems and misjudge their difficulty. Early on,
> helpers judged 47 of the 60 statements infeasible within the run's budget, yet the
> team went on to prove most of them. Human encouragement at such moments can keep
> agents from stopping too early.

and

> This result doesn't obviate the need for domain-specific harnesses or platforms.
> Prove2Me, for example, may still improve efficiency by helping agents compile Lean
> code faster and letting them search for and reuse human results.

So the two runs are complements, not a replacement: the platform gives reuse and
compilation speed, and a lead that triages and reassigns gives throughput.

### Also worth copying

- **A shared machine caps out around 100 agents.** "more than half of our 100-agent
  runs had to be stopped or restarted because memory, disk, or CPU ran out." The
  1,000-agent run used one sandbox per agent. This project runs on one phone, so the
  cap here is far lower and the lesson is about *sequencing*, not parallelism.
- **A grader on `main`.** Nothing counted as proved until Lean's checker accepted
  it, and pushing to main went through a separate merge job.
- **A restart.** Activity stopped near hour 18 and the run was restarted from a save
  with 12 more hours. Long runs are expected to break and resume.

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

## The verification chain, in detail

From the Lean4 Academy write-up of the same release
(<https://academy.lean4.dev/proofs/fermats-last-theorem>) and the proof
repository, the released artifact carries four separate checks, and they are worth
copying one by one because each catches a different class of error:

1. **A clean build.** The repository reports the project builds from scratch.
2. **An axiom audit.** `FinalCheck.lean` prints the axioms the final declaration
   depends on and they are Lean's three standard ones. This is the check that would
   catch a `sorry` or an `axiom` smuggled in anywhere in the dependency tree.
3. **A statement comparison.** A [comparator](https://github.com/leanprover/comparator)
   confirms the proved statement is *the same statement* as Mathlib's, rather than a
   weakening of it that happens to typecheck. For an upstream-pinned goal this is
   nearly free; it is also the check that stops the most damaging failure mode,
   which is proving something adjacent.
4. **A second kernel.** A patched version of [nanoda](https://github.com/ammkrn/nanoda_lib),
   a Rust implementation of the Lean kernel, re-checked the declarations
   independently of Lean's own kernel.

That fourth check is the one this project does not do and could not do cheaply on a
phone. Its value is that it does not trust the elaborator: if the proof term is
wrong in a way Lean's kernel would accept because of a bug, a second kernel
disagrees.

The Academy page also states the framing plainly, which is the same point
`REACH.md` makes about certificates:

> A formalization of a known theorem. It does not replace Wiles's discovery or erase
> the community work on which it builds.

and, about the campaign itself, that it is "an automation milestone built on human
proofs, Mathlib, and earlier formalization projects". The page is explicit that it
did not rebuild the artifact.

## Buzzard's response, and the distinction he draws

Buzzard's own write-up is at
<https://xenaproject.wordpress.com/2026/09/04/flt-anthropic-has-beaten-me-to-it/>.
The Academy page summarises it: he

> welcomed the achievement while explaining why useful, maintainable mathematical
> libraries remain a separate goal.

That distinction matters here. A proof that a checker accepts is not the same
artifact as a library a human can use, and this project has been producing the
first kind while sometimes reporting it as the second.

## The three reasons listed on the platform's own page, as a design brief

Prove2Me is described on the Anthropic page as helping in exactly three ways, and
each one implies something about how to use it:

| the platform provides | which means the workflow should be |
| --- | --- |
| a DAG of statements agents read to choose their next target | pick leaves from the frontier; do not assign angles |
| statements and proofs in separate files with independent links | work one `Thm_`/`Sol_` pair at a time; the small unit is the point |
| a natural-language description per statement, for search and reuse | search by meaning before reproving; reuse is the intended path |

The third is the one this project has used least. Every consumer theorem is a
description that another agent can find, and re-deriving a lemma that is already on
the platform is pure waste — which is exactly the failure this development has
recorded repeatedly under the heading "rediscovery".
