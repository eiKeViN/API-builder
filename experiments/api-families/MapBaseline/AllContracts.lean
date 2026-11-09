module
public import MapBaseline.Handwritten
public import MapBaseline.Macro
public import MapBaseline.Recipe
public meta import MapBaseline.Contract

#map_contract MapBaseline.Handwritten.GroupAPI against MapBaseline.Handwritten.GroupAPI
#map_contract MapBaseline.Handwritten.RingAPI against MapBaseline.Handwritten.RingAPI
#map_contract MapBaseline.Handwritten.ModuleAPI against MapBaseline.Handwritten.ModuleAPI
#map_contract MapBaseline.Macro.GroupAPI against MapBaseline.Handwritten.GroupAPI
#map_contract MapBaseline.Macro.RingAPI against MapBaseline.Handwritten.RingAPI
#map_contract MapBaseline.Macro.ModuleAPI against MapBaseline.Handwritten.ModuleAPI
#map_contract MapBaseline.Recipe.GroupAPI against MapBaseline.Handwritten.GroupAPI
#map_contract MapBaseline.Recipe.RingAPI against MapBaseline.Handwritten.RingAPI
#map_contract MapBaseline.Recipe.ModuleAPI against MapBaseline.Handwritten.ModuleAPI
