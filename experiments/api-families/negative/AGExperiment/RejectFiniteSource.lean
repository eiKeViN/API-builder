module
public import AGExperiment.Tests
public meta import AGExperiment.Install

-- Expected compilation failure: no source-locality capability was supplied.
install_scheme_property_source AGExperiment.ProbeFinite
