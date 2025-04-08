import Lean
open Lean Widget

@[widget_module]
def Widget : Widget.Module where
  javascript := include_str ".." / ".." / ".lake" / "build" / "js" / "Widget1.js"

structure WidgetProps where -- Should match 'Props' type for the React Component
  prop1 : Option String := none -- Overridden by prop below
  prop2 : Option String := some "Lean default prop" -- Overrides default prop in js
  prop3 : Option String := none -- 'null' will not override default prop in js
  deriving Server.RpcEncodable

#widget Widget with { prop1 := "Example prop" : WidgetProps }
