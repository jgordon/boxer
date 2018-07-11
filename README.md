# Boxer

This Git repository contains a copy of the C&C parser and Boxer, from
the now-unavailable official Subversion repository, for use with USC's
natural language interpretation pipelines:
- [Interpret](https://github.com/jgordon/interpret)
- [Metaphor ADP](https://github.com/isi-metaphor/Metaphor-ADP)

This is based on SVN version 2524, with updates from SVN version 2614M
-- see Christoph Rzymski's [repository](https://github.com/chrzyki/candc)
-- selectively applied. The differences from that version of Boxer
include:
- Doesn't require the use of semantic roles.
- Doesn't merge compound nouns into a single predicate with `~`, e.g.,
  `(air~force-nn e42 x19)`, when using `--elimeq`. If you want this
  behavior, uncomment the rule in `betaConversionDRT.pl`.
- Produces parses for some sentences where the later version dies.
