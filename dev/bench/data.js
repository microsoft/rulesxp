window.BENCHMARK_DATA = {
  "lastUpdate": 1765215953574,
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
      },
      {
        "commit": {
          "author": {
            "email": "git@talagrand.org",
            "name": "Eugene Talagrand",
            "username": "talagrand"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "8effca3e97f22dc154ffa4a8732ff3032a6930a6",
          "message": "ci: Azure DevOps bridge pipeline fix - address ADO requirements",
          "timestamp": "2025-12-08T09:43:11-08:00",
          "tree_id": "d8c23f294ba58a17845dec7106ef6944b4145827",
          "url": "https://github.com/microsoft/rulesxp/commit/8effca3e97f22dc154ffa4a8732ff3032a6930a6"
        },
        "date": 1765215953264,
        "tool": "cargo",
        "benches": [
          {
            "name": "Parsing/Scheme Simple",
            "value": 843,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Nested",
            "value": 3558,
            "range": "± 27",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Factorial",
            "value": 9496,
            "range": "± 23",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Simple",
            "value": 464,
            "range": "± 1",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Nested",
            "value": 1892,
            "range": "± 3",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Simple",
            "value": 2025,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Simple",
            "value": 2005,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Nested",
            "value": 2394,
            "range": "± 8",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Nested",
            "value": 2309,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Factorial",
            "value": 142844,
            "range": "± 534",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}