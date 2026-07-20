# Primary Rouché checker rerun

Command executed from the extracted causal-completion package root:

```bash
python OBS_matched_subdivision_interval_checker.py
```

Environment:

- Python 3.12
- python-flint 0.9.0

Result: exit code 0. The full JSON output is in `OBS_Primary_Rouche_Check_v0.2.4.log` and reproduces the manuscript bounds, including visibility lower bound 47.020348992241, leadership gap lower bound 39.727092946595, and `Y < 0.901947534017196`.
