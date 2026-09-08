import Lake
open Lake DSL

-- A package whose own `Errata.run` script is found first, so Verso's driver must be qualified.
package app

require verso from "../../../.."

namespace Errata
script run (_args) do
  return 0
end Errata
