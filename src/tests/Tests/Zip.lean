import VersoUtil.Zip

open Verso.Zip



def testExtract (files : Array (String × ByteArray)) (method : CompressionMethod) : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let file := dir / "out.zip"
    zipToFile file files method
    let out ← IO.Process.output {cmd := "unzip", args := #["-u", file.toString]}
    -- unzip returns 1 on empty archives, 2 on corrupt archives
    if out.exitCode == 0 || (files.isEmpty && out.exitCode == 1) then
      for (f, contents) in files do
        let found ← IO.FS.readBinFile f
        if found != contents then
          throw <| .userError s!"Mismatched file contents of {f}"
    else
      throw <| IO.userError s!"process 'unzip' exited with code {out.exitCode}\
        \nstderr:\
        \n{out.stderr}"
