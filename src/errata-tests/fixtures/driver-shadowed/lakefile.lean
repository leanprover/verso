import Lake
open Lake DSL

-- A package whose own `Errata.run` script is found first, so Verso's driver must be qualified.
package app where
  -- Verso's clones of the git dependencies serve this workspace too, so that the modules built from
  -- the shared Verso checkout see the same dependency paths from both.
  packagesDir := "../../../../.lake/packages"

require verso from "../../../.."

-- A test, which the editor widget's invocation of Verso's driver runs.
lean_lib Shadowed

namespace Errata
script run (_args) do
  return 0
end Errata
