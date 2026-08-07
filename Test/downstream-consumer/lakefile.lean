-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Lake
open Lake DSL System

/-!
Regression fixture for "Using cpsat as a dependency" in the README: a
downstream package that only `require`s cpsat and builds a normal `lean_exe`.
Lake does not propagate a package's `weakLinkArgs`/`weakLeancArgs` to a
consumer's own targets (see the README section), so this mirrors the exact
snippet documented there. If that snippet ever drifts out of sync with what
cpsat's own `lakefile.lean` needs, this fixture fails to link and catches it.
-/

-- Relative, unlike `cpsatDir` below: this is what gets snapshotted into
-- `lake-manifest.json`, so it must stay portable across checkouts rather than
-- baking in this machine's absolute path.
def cpsatRelDir : FilePath := ".." / ".."
def cpsatDir : FilePath := __dir__ / cpsatRelDir
def orToolsLib : FilePath := cpsatDir / "or-tools" / "build" / "lib"

package downstreamConsumer where
  weakLeancArgs := #["-I", (cpsatDir / "or-tools").toString]
  weakLinkArgs := #[
    "-L", orToolsLib.toString, "-lortools", "-lortools_core", s!"-Wl,-rpath,{orToolsLib}"
  ]

require cpsat from cpsatRelDir

@[default_target]
lean_exe downstreamConsumer where
  root := `Main
