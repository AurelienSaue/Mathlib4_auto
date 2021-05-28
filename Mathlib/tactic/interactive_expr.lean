/-
Copyright (c) 2020 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/
import Mathlib.PrePort
import Mathlib.Lean3Lib.init.default
import Mathlib.PostPort

namespace Mathlib

/-!
# Widgets used for tactic state and term-mode goal display

The vscode extension supports the display of interactive widgets.
Default implementation of these widgets are included in the core
library.  We override them here using `vm_override` so that we can
change them quickly without waiting for the next Lean release.

The function `widget_override.interactive_expression.mk` renders a single
expression as a widget component.  Each goal in a tactic state is rendered
using the `widget_override.tactic_view_goal` function,
a complete tactic state is rendered using
`widget_override.tactic_view_component`.

Lean itself calls the `widget_override.term_goal_widget` function to render
term-mode goals and `widget_override.tactic_state_widget` to render the
tactic state in a tactic proof.
-/

namespace widget_override


namespace interactive_expression


