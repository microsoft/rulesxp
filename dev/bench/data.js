window.BENCHMARK_DATA = {
  "lastUpdate": 1769974935893,
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
      },
      {
        "commit": {
          "author": {
            "email": "49699333+dependabot[bot]@users.noreply.github.com",
            "name": "dependabot[bot]",
            "username": "dependabot[bot]"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "3b83127c38a3585749b6f56cf1d23b9dcfec7da9",
          "message": "ci(deps): bump actions/upload-artifact from 5 to 6\n\nBumps [actions/upload-artifact](https://github.com/actions/upload-artifact) from 5 to 6.\n- [Release notes](https://github.com/actions/upload-artifact/releases)\n- [Commits](https://github.com/actions/upload-artifact/compare/v5...v6)\n\n---\nupdated-dependencies:\n- dependency-name: actions/upload-artifact\n  dependency-version: '6'\n  dependency-type: direct:production\n  update-type: version-update:semver-major\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>",
          "timestamp": "2026-01-02T20:19:55-08:00",
          "tree_id": "f392784c39c5638da7c321f94eda5459fa1c56c3",
          "url": "https://github.com/microsoft/rulesxp/commit/3b83127c38a3585749b6f56cf1d23b9dcfec7da9"
        },
        "date": 1767414160432,
        "tool": "cargo",
        "benches": [
          {
            "name": "Parsing/Scheme Simple",
            "value": 780,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Nested",
            "value": 3552,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Factorial",
            "value": 9486,
            "range": "± 54",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Simple",
            "value": 441,
            "range": "± 2",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Nested",
            "value": 1914,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Simple",
            "value": 1974,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Simple",
            "value": 1919,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Nested",
            "value": 2332,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Nested",
            "value": 2236,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Factorial",
            "value": 138801,
            "range": "± 686",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "49699333+dependabot[bot]@users.noreply.github.com",
            "name": "dependabot[bot]",
            "username": "dependabot[bot]"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7032d79f17533bdc16e5b4c0f405fcf840bdcee8",
          "message": "deps(deps): bump serde_json from 1.0.145 to 1.0.148 (#13)\n\nBumps [serde_json](https://github.com/serde-rs/json) from 1.0.145 to 1.0.148.\n- [Release notes](https://github.com/serde-rs/json/releases)\n- [Commits](https://github.com/serde-rs/json/compare/v1.0.145...v1.0.148)\n\n---\nupdated-dependencies:\n- dependency-name: serde_json\n  dependency-version: 1.0.148\n  dependency-type: direct:production\n  update-type: version-update:semver-patch\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>\nCo-authored-by: dependabot[bot] <49699333+dependabot[bot]@users.noreply.github.com>\nCo-authored-by: Eugene <git@talagrand.org>",
          "timestamp": "2026-01-03T04:21:38Z",
          "tree_id": "4b46ab52246830cd1e1d9096614287191ce1f6fc",
          "url": "https://github.com/microsoft/rulesxp/commit/7032d79f17533bdc16e5b4c0f405fcf840bdcee8"
        },
        "date": 1767414260208,
        "tool": "cargo",
        "benches": [
          {
            "name": "Parsing/Scheme Simple",
            "value": 811,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Nested",
            "value": 3610,
            "range": "± 45",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Factorial",
            "value": 9634,
            "range": "± 40",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Simple",
            "value": 480,
            "range": "± 6",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Nested",
            "value": 1969,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Simple",
            "value": 2091,
            "range": "± 9",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Simple",
            "value": 1989,
            "range": "± 15",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Nested",
            "value": 2395,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Nested",
            "value": 2352,
            "range": "± 4",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Factorial",
            "value": 146217,
            "range": "± 495",
            "unit": "ns/iter"
          }
        ]
      },
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
          "id": "fb24626ad0316abdac2d0fe10c592faeaf6317cc",
          "message": "Merge pull request #14 from microsoft/dependabot/cargo/criterion-0.8.1\n\ndeps(deps): bump criterion from 0.5.1 to 0.8.1",
          "timestamp": "2026-01-02T20:40:58-08:00",
          "tree_id": "cacf14347984ce71b7c9cd64bd98f99b637c52ad",
          "url": "https://github.com/microsoft/rulesxp/commit/fb24626ad0316abdac2d0fe10c592faeaf6317cc"
        },
        "date": 1767415417373,
        "tool": "cargo",
        "benches": [
          {
            "name": "Parsing/Scheme Simple",
            "value": 801,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Nested",
            "value": 3614,
            "range": "± 22",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Factorial",
            "value": 9573,
            "range": "± 32",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Simple",
            "value": 452,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Nested",
            "value": 1877,
            "range": "± 41",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Simple",
            "value": 2007,
            "range": "± 14",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Simple",
            "value": 1920,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Nested",
            "value": 2375,
            "range": "± 94",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Nested",
            "value": 2338,
            "range": "± 112",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Factorial",
            "value": 139956,
            "range": "± 805",
            "unit": "ns/iter"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "49699333+dependabot[bot]@users.noreply.github.com",
            "name": "dependabot[bot]",
            "username": "dependabot[bot]"
          },
          "committer": {
            "email": "git@talagrand.org",
            "name": "Eugene",
            "username": "talagrand"
          },
          "distinct": true,
          "id": "da94c104faae68d0ec80f1ad5f8d695afc590db9",
          "message": "deps(deps): bump serde_json from 1.0.148 to 1.0.149\n\nBumps [serde_json](https://github.com/serde-rs/json) from 1.0.148 to 1.0.149.\n- [Release notes](https://github.com/serde-rs/json/releases)\n- [Commits](https://github.com/serde-rs/json/compare/v1.0.148...v1.0.149)\n\n---\nupdated-dependencies:\n- dependency-name: serde_json\n  dependency-version: 1.0.149\n  dependency-type: direct:production\n  update-type: version-update:semver-patch\n...\n\nSigned-off-by: dependabot[bot] <support@github.com>",
          "timestamp": "2026-02-01T11:39:33-08:00",
          "tree_id": "eca53edf601e5dd1e6c176f53ccdedc2713fbe9b",
          "url": "https://github.com/microsoft/rulesxp/commit/da94c104faae68d0ec80f1ad5f8d695afc590db9"
        },
        "date": 1769974935518,
        "tool": "cargo",
        "benches": [
          {
            "name": "Parsing/Scheme Simple",
            "value": 674,
            "range": "± 13",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Nested",
            "value": 3085,
            "range": "± 18",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/Scheme Factorial",
            "value": 8476,
            "range": "± 188",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Simple",
            "value": 409,
            "range": "± 5",
            "unit": "ns/iter"
          },
          {
            "name": "Parsing/JSONLogic Nested",
            "value": 1667,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Simple",
            "value": 2164,
            "range": "± 33",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Simple",
            "value": 2048,
            "range": "± 39",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Nested",
            "value": 2317,
            "range": "± 11",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval JSONLogic Nested",
            "value": 2285,
            "range": "± 7",
            "unit": "ns/iter"
          },
          {
            "name": "Evaluation/Eval Scheme Factorial",
            "value": 143081,
            "range": "± 2259",
            "unit": "ns/iter"
          }
        ]
      }
    ]
  }
}