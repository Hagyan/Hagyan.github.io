# Restore the saved finite proof object

The public source snapshot carries [summary-arithmetic-demo.json.gz](summary-arithmetic-demo.json.gz) as a deterministic gzip file. In this directory, run:

~~~sh
gzip -dk summary-arithmetic-demo.json.gz
sha256sum summary-arithmetic-demo.json
~~~

The uncompressed SHA-256 must be c50fbd13492669ee3480ff5702966ae88974b57fc67b95f81f170ee79c7f290a. The generated JSON is the saved 204-rule, 407-join **experimental local** arithmetic certificate. Its replay is not an exact PA-bin Bew or Enderton proof. The copy of the project used for the fresh Lean audit held the uncompressed JSON.
