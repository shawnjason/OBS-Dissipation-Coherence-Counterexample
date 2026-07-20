# DOI Metadata Patch Before `v1.0.0`

Once the paper DOI is reserved, add the following object to `.zenodo.json` before the first GitHub release:

```json
"related_identifiers": [
  {
    "identifier": "10.xxxx/PAPER-DOI",
    "relation": "isSupplementTo",
    "resource_type": "publication-preprint"
  }
]
```

Place it before the final closing brace and ensure the preceding field ends with a comma.

Also add this line under the `preferred-citation` block in `CITATION.cff`:

```yaml
  doi: "10.xxxx/PAPER-DOI"
```

After Zenodo archives GitHub release `v1.0.0`, add the resulting software DOI to the paper record using the reciprocal relation `Is supplemented by`.
