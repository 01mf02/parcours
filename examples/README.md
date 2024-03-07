Howdy!
So you would like to learn how to write a parser with parcours?
You have come to the right place!
This directory contains a few examples that show the usage of parcours.
These examples are, in order of increasing complexity:

* `json.rs`: A JSON value parser.
  Shows how to create recursive parsers.
* `lambda.rs`: A lambda expression parser.
  Shows how to use the mutable state, among others to report parse errors.
* `bc.rs`: A `bc`-style command-line calculator.
  Shows how to separate lexing from parsing and
  how to parse binary operators with precedence climbing.
