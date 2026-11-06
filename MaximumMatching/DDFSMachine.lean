import MaximumMatching.DDFSRun

/-! Concrete mode transitions for the DDFS stacks, collision recovery and
Barrier. Edge order is nondeterministic; every scan requires an unexplored
edge. The invariant and termination proofs are separate modules. -/
namespace MaximumMatching.DDFS.Machine
variable {V : Type} {H : LayeredGraph V}

inductive Mode (H : LayeredGraph V) where
  | normal
  | redRecovery (b : V) (savedRed savedGreen : Path H)
  | greenRecovery (b : V) (savedRed savedGreen : Path H)
  | disjoint
  | bottleneck (b : V) (redPath greenPath : Path H)

structure State (H : LayeredGraph V) where
  frame : SearchFrame H
  mode : Mode H

def initial (H : LayeredGraph V) (r g : V) : State H :=
  ⟨SearchFrame.initial H r g, .normal⟩

def Terminal (s : State H) : Prop :=
  (s.mode = .disjoint) ∨ ∃ b p q, s.mode = .bottleneck b p q

/-- All operations of the coordinated stack machine. Scanning a previously
visited destination skips it only during recovery; in normal mode the depth
invariant proves it is precisely the other activity center, hence a collision.
The candidate's outgoing edges are not scanned during recovery. -/
inductive Step : State H → State H → Prop where
  /-- Equal roots are a mathematical bottleneck. In the MV wrapper this branch
  corresponds to the immediate same-bud abort with no new petal (§4.3). -/
  | sameRoot (s : State H) (hn : s.mode = .normal)
      (hr : s.frame.red.length = 0) (hg : s.frame.green.length = 0)
      (heq : s.frame.red.last = s.frame.green.last) :
      Step s { s with mode := .bottleneck s.frame.red.last s.frame.red s.frame.green }
  | redMove (s : State H) (hn : s.mode = .normal)
      (hne : s.frame.red.last ≠ s.frame.green.last)
      (hsched : H.level s.frame.green.last ≤ H.level s.frame.red.last)
      (v : V) (he : H.Edge s.frame.red.last v)
      (hu : ¬s.frame.explored s.frame.red.last v)
      (hv : ¬s.frame.visited v ∨ v = s.frame.green.last) :
      Step s { frame := s.frame.advanceRed v he, mode := .normal }
  | greenMove (s : State H) (hn : s.mode = .normal)
      (hne : s.frame.red.last ≠ s.frame.green.last)
      (hsched : H.level s.frame.red.last < H.level s.frame.green.last)
      (v : V) (he : H.Edge s.frame.green.last v)
      (hu : ¬s.frame.explored s.frame.green.last v)
      (hv : ¬s.frame.visited v ∨ v = s.frame.red.last) :
      Step s { frame := s.frame.advanceGreen v he, mode := .normal }
  | bottom (s : State H) (hn : s.mode = .normal)
      (hne : s.frame.red.last ≠ s.frame.green.last)
      (hr : H.level s.frame.red.last = 0) (hg : H.level s.frame.green.last = 0) :
      Step s { s with mode := .disjoint }
  | collision (s : State H) (hn : s.mode = .normal)
      (heq : s.frame.red.last = s.frame.green.last)
      (hroots : s.frame.red.first ≠ s.frame.green.first) :
      Step s { s with mode := .redRecovery s.frame.red.last s.frame.red s.frame.green }
  | redPop (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hpos : 0 < s.frame.red.length) (hbar : s.frame.red.last ≠ s.frame.barrier)
      (hex : s.frame.red.last = b ∨ s.frame.Exhausted s.frame.red.last) :
      Step s { frame := s.frame.backtrackRed hpos, mode := s.mode }
  | redSkip (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hhigh : H.level b < H.level s.frame.red.last)
      (v : V) (he : H.Edge s.frame.red.last v)
      (hu : ¬s.frame.explored s.frame.red.last v) (hv : s.frame.visited v) :
      Step s { frame := s.frame.scanRed v, mode := s.mode }
  | redDeeper (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hhigh : H.level b < H.level s.frame.red.last)
      (v : V) (he : H.Edge s.frame.red.last v)
      (hu : ¬s.frame.explored s.frame.red.last v) (hv : ¬s.frame.visited v)
      (hvhigh : H.level b < H.level v) :
      Step s { frame := s.frame.advanceRed v he, mode := s.mode }
  | redEscape (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hhigh : H.level b < H.level s.frame.red.last)
      (v : V) (he : H.Edge s.frame.red.last v)
      (hu : ¬s.frame.explored s.frame.red.last v) (hv : ¬s.frame.visited v)
      (hvlow : H.level v ≤ H.level b) :
      Step s { frame := s.frame.advanceRed v he, mode := .normal }
  | redFail (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .redRecovery b p q)
      (hbar : s.frame.red.last = s.frame.barrier)
      (hex : s.frame.red.last = b ∨ s.frame.Exhausted s.frame.red.last) :
      Step s { frame := s.frame.restoreRed p b, mode := .greenRecovery b p q }
  | greenPop (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hpos : 0 < s.frame.green.length)
      (hex : s.frame.green.last = b ∨ s.frame.Exhausted s.frame.green.last) :
      Step s { frame := s.frame.backtrackGreen hpos, mode := s.mode }
  | greenSkip (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hhigh : H.level b < H.level s.frame.green.last)
      (v : V) (he : H.Edge s.frame.green.last v)
      (hu : ¬s.frame.explored s.frame.green.last v) (hv : s.frame.visited v) :
      Step s { frame := s.frame.scanGreen v, mode := s.mode }
  | greenDeeper (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hhigh : H.level b < H.level s.frame.green.last)
      (v : V) (he : H.Edge s.frame.green.last v)
      (hu : ¬s.frame.explored s.frame.green.last v) (hv : ¬s.frame.visited v)
      (hvhigh : H.level b < H.level v) :
      Step s { frame := s.frame.advanceGreen v he, mode := s.mode }
  | greenEscape (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hhigh : H.level b < H.level s.frame.green.last)
      (v : V) (he : H.Edge s.frame.green.last v)
      (hu : ¬s.frame.explored s.frame.green.last v) (hv : ¬s.frame.visited v)
      (hvlow : H.level v ≤ H.level b) :
      Step s { frame := s.frame.advanceGreen v he, mode := .normal }
  | greenFail (s : State H) (b : V) (p q : Path H)
      (hm : s.mode = .greenRecovery b p q)
      (hroot : s.frame.green.length = 0)
      (hex : s.frame.green.last = b ∨ s.frame.Exhausted s.frame.green.last) :
      Step s { s with mode := .bottleneck b p q }

inductive Reachable (r g : V) : State H → Prop where
  | initial : Reachable r g (initial H r g)
  | step {s t} : Reachable r g s → Step s t → Reachable r g t

end MaximumMatching.DDFS.Machine
