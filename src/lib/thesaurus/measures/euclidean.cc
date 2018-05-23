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
#include <algorithm>

#include <iostream>
#include <iomanip>
#include <fstream>
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

#include "thesaurus/match.h"
#include "thesaurus/measure.h"
#include "thesaurus/explain.h"

#include "thesaurus/measures/euclidean.h"

namespace NLP { namespace Thesaurus {

float
MEuclidean::measure(const Object *const obj1, const Object *const obj2) const {
  const Relations &r1 = obj1->relations;
  const Relations &r2 = obj2->relations;

  Relations::const_iterator i = r1.begin();
  Relations::const_iterator j = r2.begin();

  float total = 0;
  while(i != r1.end() && j != r2.end()){
    if(i->equal(*j)){
      // we have an identical relation
      float diff = i->score() - j->score();
      total += diff*diff;
      i++;
      j++;
    }else if(i->compare(*j) < 0){
      total += i->score()*i->score();
      i++;
    }else{
      total += j->score()*j->score();
      j++;
    }
  }
  for( ; i != r1.end(); ++i)
    total += i->score()*i->score();
  for( ; j != r2.end(); ++j)
    total += j->score()*j->score();
  return -sqrt(total);
}

bool
MEuclidean::heuristic(const Object *const obj1, const Object *const obj2) const {
  const vector<Relation *> &r1 = obj1->canonical;
  const vector<Relation *> &r2 = obj2->canonical;

  vector<Relation *>::const_iterator i = r1.begin();
  vector<Relation *>::const_iterator j = r2.begin();
  while(i != r1.end() && j != r2.end()){
    if((*i)->equal(*j))
      return true;
    else if((*i)->compare(*j) < 0)
      i++;
    else
      j++;
  }
  return false;
}

void
MEuclidean::explain(std::ostream &out, const Object *const obj1, const Object *const obj2) const {
  float num = 0;
  float denom = 1;
  float s1 = 0;
  float s2 = 0;
  ulong ncommon = 0;
  ulong n1 = 0;
  ulong n2 = 0;

  if(!use_heuristic || heuristic(obj1, obj2)){
    const Relations &r1 = obj1->relations;
    const Relations &r2 = obj2->relations;

    Relations::const_iterator i = r1.begin();
    Relations::const_iterator j = r2.begin();

    out << obj1->str() << " and " << obj2->str() << " share the following terms:\n";
    while(i != r1.end() && j != r2.end()){
      if(i->equal(*j)){
        // we have an identical relation
        print_equal(out, i, j);
        float diff = i->score() - j->score();
        num += diff*diff;
        ncommon++;
        i++;
        j++;
      }else if(i->compare(*j) < 0){
        print_unequal(out, obj1, i);
        s1 += i->score()*i->score();
        n1++;
        i++;
      }else{
        print_unequal(out, obj2, j);
        s2 += j->score()*j->score();
        n2++;
        j++;
      }
    }
    n1 += r1.end() - i;
    for( ; i != r1.end(); ++i)
      s1 += i->score()*i->score();
    n2 += r2.end() - j;
    for( ; j != r2.end(); ++j)
      s2 += j->score()*j->score();

    print_common(out, ncommon, num, 1.0);
    print_unique(out, obj1, n1, s1);
    print_unique(out, obj2, n2, s2);
    num += s1 + s2;
    print_score(out, "Euclidean", sqrt(num), denom);
  }else
    print_failed(out, obj1, obj2);
}

} }
