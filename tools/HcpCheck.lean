module

import Tools.HcpCheck

/-- `lake exe hcp-check`: the HCP ladder's checker, `--sbvr SBVR_CHECK` the pinned binary as a subprocess. -/
public def main (args : List String) : IO UInt32 := Tools.HcpCheck.main args
