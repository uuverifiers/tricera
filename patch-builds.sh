#!/usr/bin/env bash
set -e

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "Patching local submodules under $ROOT_DIR ..."

############################################
# Patch eldarica build.sbt
############################################
ELDARICA_BUILD="$ROOT_DIR/eldarica/build.sbt"

if [[ -f "$ELDARICA_BUILD" ]]; then
  if ! grep -q 'ProjectRef(file("../princess"), "root")' "$ELDARICA_BUILD"; then
    echo "  -> Patching eldarica/build.sbt"

    # Insert the line between dependsOn(...) and .settings(...)
    awk '
      /dependsOn\(tplspecParser\)\./ {
        print "    dependsOn(ProjectRef(file(\"../princess\"), \"root\"))."
      }
      { print }
    ' "$ELDARICA_BUILD" > "$ELDARICA_BUILD.tmp" && mv "$ELDARICA_BUILD.tmp" "$ELDARICA_BUILD"
  else
    echo "  -> eldarica/build.sbt already patched"
  fi
else
  echo "  !! eldarica/build.sbt not found"
fi


############################################
# Patch horn-concurrency build.sbt
############################################
HORN_BUILD="$ROOT_DIR/horn-concurrency/build.sbt"

if [[ -f "$HORN_BUILD" ]]; then
  if ! grep -q 'ProjectRef(file("../eldarica"), "root")' "$HORN_BUILD"; then
    echo "  -> Patching horn-concurrency/build.sbt"

    # Append after the main project definition
    awk '
      /lazy val root = \(project in file\("\."\)\)\./ {
        print $0 "\n  dependsOn(ProjectRef(file(\"../eldarica\"), \"root\"))."
        next
      }
      { print }
    ' "$HORN_BUILD" > "$HORN_BUILD.tmp" && mv "$HORN_BUILD.tmp" "$HORN_BUILD"
  else
    echo "  -> horn-concurrency/build.sbt already patched"
  fi
else
  echo "  !! horn-concurrency/build.sbt not found"
fi

echo "Done."
