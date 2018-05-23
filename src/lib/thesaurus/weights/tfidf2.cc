// C&C NLP tools
// Copyright (c) Universities of Edinburgh, Oxford and Sydney
// Copyright (c) James R. Curran
//
// This software is covered by a non-commercial use licence.
// See LICENCE.txt for the full text of the licence.
//
// If LICENCE.txt is not included in this distribution
// please email candc@it.usyd.edu.au to obtain a copy.

#include <cmath>
#include <string>
#include <vector>

#include <iostream>
#include <iomanip>
#include <stdexcept>

using namespace std;

#include "except.h"
#include "utils.h"
#include "utils/io.h"

#include "hash.h"
#include "pool.h"

#include "hashtable/entry.h"

#include "thesaurus/options.h"
#include "thesaurus/type.h"
#include "thesaurus/types.h"
#include "thesaurus/attribute.h"
#include "thesaurus/attributes.h"
#include "thesaurus/weight.h"
#include "thesaurus/relation.h"
#include "thesaurus/object.h"
#include "thesaurus/objects.h"
#include "thesaurus/weights/utils.h"

namespace NLP { namespace Thesaurus {

class WTFIDF2: public Weight {
public:
  WTFIDF2(void): Weight("tfidf2.cc", "TFIDF2", "log2(f(r) + 1)/log2(1 + 1/q(a))") {};
  ~WTFIDF2(void) {};

  float operator()(const Object *o, const Attribute *a, const Relation *r) const;
};

float
WTFIDF2::operator()(const Object *o, const Attribute *a, const Relation *r) const {
  return log2(f(r) + 1)/log2(1 + 1/q(a));
}

} }
