window.BENCHMARK_DATA = {
  "lastUpdate": 1764724095833,
  "repoUrl": "https://github.com/microsoft/rulesxp",
  "entries": {
    "RulesXP Benchmark": [
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene",
            "username": "talagrand"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "77f16f1dee703be7a3211ecc1a0c624f764b3418",
          "message": "Merge pull request #8 from talagrand/benches\n\nAdd perf benches; flatten project structure",
          "timestamp": "2025-12-02T17:05:29-08:00",
          "tree_id": "53d3a08a278fa4b9c4b4b86e8e5b9304fa622250",
          "url": "https://github.com/microsoft/rulesxp/commit/77f16f1dee703be7a3211ecc1a0c624f764b3418"
        },
        "date": 1764724095568,
        "tool": "cargo",
        "benches": [
          {
            "name": "Parsing/Scheme Simple",
            "value": 768,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Nested",
            "value": 3509,
            "range": "± 45",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Factorial",
            "value": 9335,
            "range": "± 53",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Simple",
            "value": 492,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Nested",
            "value": 1938,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Simple",
            "value": 2031,
            "range": "± 10",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Simple",
            "value": 1937,
            "range": "± 28",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Nested",
            "value": 2304,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Nested",
            "value": 2326,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Factorial",
            "value": 140645,
            "range": "± 679",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}