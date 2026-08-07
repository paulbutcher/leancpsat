-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Lake
open Lake DSL

/-!
Regression fixture for "Using cpsat as a dependency" in the README: a
downstream package that only `require`s cpsat and builds a normal `lean_exe`,
with no linker configuration of its own. cpsat's `moreLinkLibs`/`moreLinkObjs`
(see `lakefile.lean` at the repo root) are what make this link and run; if
that propagation ever breaks, this fixture fails to build.
-/

package downstreamConsumer

require cpsat from "../.."

@[default_target]
lean_exe downstreamConsumer where
  root := `Main
