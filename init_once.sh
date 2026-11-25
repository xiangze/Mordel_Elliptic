rm -rf .lake/packages lake-manifest.json
lake update
lake exe cache get
lake build