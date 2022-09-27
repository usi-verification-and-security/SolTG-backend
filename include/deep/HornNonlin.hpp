#ifndef HORNNONLIN__HPP__
#define HORNNONLIN__HPP__

#include "ae/AeValSolver.hpp"

using namespace std;
using namespace boost;

namespace ufo
{
  // all adapted from Horn.hpp; experimental; to merge with Horn.hpp at some point
  inline bool rewriteHelperConsts_nonlinear(Expr& body, Expr v1, Expr v2)
  {
    if (isOpX<MPZ>(v1))
    {
      body = mk<AND>(body, mk<EQ>(v1, v2));
      return true;
    }
    else if (isOpX<TRUE>(v1))
    {
      body = mk<AND>(body, v2);
      return true;
    }
    else if (isOpX<FALSE>(v1))
    {
      body = mk<AND>(body, mk<NEG>(v2));
      return true;
    }
    return false;
  }

  struct HornRuleExt
  {
    vector<ExprVector> srcVars;
    ExprVector dstVars;
    ExprVector locVars;

    Expr body;
    Expr head;

    ExprVector srcRelations;
    Expr dstRelation;

    bool isFact;
    bool isQuery;
    bool isInductive;
    map<int, Expr> arg_names;

    void assignVarsAndRewrite (vector<ExprVector>& _srcVars, vector<ExprVector>& invVarsSrc,
                               ExprVector& _dstVars, ExprVector& invVarsDst)
    {
      for (int i = 0; i < _srcVars.size(); i++)
      {
        ExprVector tmp;
        for (int j = 0; j < _srcVars[i].size(); j++)
        {
          tmp.push_back(invVarsSrc[i][j]);
          body = mk<AND>(body, mk<EQ>(_srcVars[i][j], tmp[j]));
        }
        srcVars.push_back(tmp);
      }

      for (int i = 0; i < _dstVars.size(); i++)
      {
        // primed copy of var:
        Expr new_name = mkTerm<string> (lexical_cast<string>(invVarsDst[i]) + "'", body->getFactory());
        Expr var = cloneVar(invVarsDst[i], new_name);
        dstVars.push_back(var);
        body = mk<AND>(body, mk<EQ>(_dstVars[i], dstVars[i]));
        arg_names[i] = _dstVars[i];
      }
    }
  };

  class CHCs
  {
    private:
    set<int> indeces;
    string varname = "_FH_";

    public:

    ExprFactory &m_efac;
    EZ3 &m_z3;

    ExprSet decls;
    Expr failDecl;
    vector<HornRuleExt> chcs;
    int index_fact_chc;
    vector<int> index_cycle_chc;
    map<Expr, ExprVector> invVars;
    map<Expr, vector<int>> incms;
    map<Expr, int> expr_id;
    int qCHCNum;  // index of the query in chc
    int total_var_cnt = 0;
    string infile;

      //ToDo: Remove or recheck later on; move from Horn.hpp
    int debug;

    CHCs(ExprFactory &efac, EZ3 &z3) : m_efac(efac), m_z3(z3) {};

    bool isFapp (Expr e)
    {
      if (isOpX<FAPP>(e))
        if (e->arity() > 0)
          if (isOpX<FDECL>(e->arg(0)))
            if (e->arg(0)->arity() >= 2)
              return true;
      return false;
    }

    void preprocess (Expr term, ExprVector& locVars, vector<ExprVector>& srcVars, ExprVector &srcRelations, ExprSet& lin)
    {
      if (isOpX<AND>(term))
      {
        for (auto it = term->args_begin(), end = term->args_end(); it != end; ++it)
        {
          preprocess(*it, locVars, srcVars, srcRelations, lin);
        }
      }
      else
      {
        if (bind::isBoolConst(term))
        {
          lin.insert(term);
        }
        if (isOpX<FAPP>(term) && find(locVars.begin(), locVars.end(), term) == locVars.end())
        {
          if (term->arity() > 0)
          {
            if (isOpX<FDECL>(term->arg(0)))
            {
              Expr rel = term->arg(0);
              if (rel->arity() >= 2)
              {
                addDecl(rel);
                srcRelations.push_back(rel->arg(0));
                ExprVector tmp;
                for (auto it = term->args_begin()+1, end = term->args_end(); it != end; ++it)
                  tmp.push_back(*it);
                srcVars.push_back(tmp);
              }
            }
          }
        }
        else
        {
          lin.insert(term);
        }
      }
    }

    void addDecl (Expr a)
    {
      if (invVars[a->arg(0)].empty())
      {
        decls.insert(a);
        for (int i = 1; i < a->arity()-1; i++)
        {
          Expr new_name = mkTerm<string> (varname + to_string(total_var_cnt), m_efac);
          total_var_cnt++;
          Expr arg = a->arg(i);
          if (!isOpX<INT_TY> (arg) && !isOpX<REAL_TY> (arg) && !isOpX<BOOL_TY> (arg) && !isOpX<ARRAY_TY> (arg))
          {
            errs() << "Argument #" << i << " of " << a << " is not supported\n";
            exit(1);
          }
          Expr var = fapp (constDecl (new_name, a->arg(i)));
          invVars[a->arg(0)].push_back(var);
        }
      }
    }

    bool normalize (Expr& r, HornRuleExt& hr)
    {
      r = regularizeQF(r);

      // TODO: support more syntactic replacements
      while (isOpX<FORALL>(r))
      {
        for (int i = 0; i < r->arity() - 1; i++)
        {
          hr.locVars.push_back(bind::fapp(r->arg(i)));
        }
        r = r->last();
      }

      if (isOpX<NEG>(r) && isOpX<EXISTS>(r->first()))
      {
        for (int i = 0; i < r->first()->arity() - 1; i++)
          hr.locVars.push_back(bind::fapp(r->first()->arg(i)));

        r = mk<IMPL>(r->first()->last(), mk<FALSE>(m_efac));
      }

      if (isOpX<NEG>(r))
      {
        r = mk<IMPL>(r->first(), mk<FALSE>(m_efac));
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->left()) && hasUninterp(r->left()))
      {
        r = mk<IMPL>(r->left()->left(), r->right());
      }
      else if (isOpX<OR>(r) && r->arity() == 2 && isOpX<NEG>(r->right()) && hasUninterp(r->right()))
      {
        r = mk<IMPL>(r->right()->left(), r->left());
      }

      if (isOpX<IMPL>(r) && !isFapp(r->right()) && !isOpX<FALSE>(r->right()))
      {
        if (isOpX<TRUE>(r->right()))
        {
          return false;
        }
        r = mk<IMPL>(mk<AND>(r->left(), mk<NEG>(r->right())), mk<FALSE>(m_efac));
      }

      if (!isOpX<IMPL>(r)) r = mk<IMPL>(mk<TRUE>(m_efac), r);

      return true;
    }

    bool hasOnlyInduct(Expr rel, vector<int>& indexes)
    {
      int num = 0;
      for (int i = 0; i < chcs.size(); i++)
        if (chcs[i].dstRelation == rel)
        {
          if (chcs[i].isFact)
            return false;
          bool isInd = false;
          for (auto & c : chcs[i].srcRelations)
          {
            if (c == rel)
            {
              isInd = true;
              break;
            }
          }
          if (isInd) indexes.push_back(i);
          else return false;
        }
      return indexes.size() > 0;
    }

    void computeIncms()
    {
      incms.clear();
      for (int i = 0; i < chcs.size(); i++)
        incms[chcs[i].dstRelation].push_back(i);
    }

    void prune ()
    {
      int sz = decls.size();
      set<int> toSkip;
      computeIncms();

      for (auto it = decls.begin(); it != decls.end(); )
      {
        Expr d = *it;

        vector<int> indexes;
        bool toDel = hasOnlyInduct(d->left(), indexes);
        for (int i : indexes) toSkip.insert(i);

        if (toDel || incms[d->left()].empty())
        {
          toDel = true;
          for (int i = 0; i < chcs.size(); i++)
          {
            bool isInBody = false;
            for (auto & s : chcs[i].srcRelations)
            {
              if (s == d->left())
              {
                isInBody = true;
                break;
              }
            }
            if (isInBody)
            {
              toSkip.insert(i);
            }
          }
        }

        if (toDel) it = decls.erase(it);
        else ++it;
      }
      for (auto rit = toSkip.rbegin(); rit != toSkip.rend(); rit++)
        chcs.erase(chcs.begin() + *rit);

      if (sz == decls.size()) return;
      else prune();
    }

    void parse(string smt, bool removeQuery = false)
    {
      infile = smt;
      std::unique_ptr<ufo::ZFixedPoint <EZ3> > m_fp;
      m_fp.reset (new ZFixedPoint<EZ3> (m_z3));
      ZFixedPoint<EZ3> &fp = *m_fp;
      fp.loadFPfromFile(smt);

      for (auto &r: fp.m_rules)
      {
        chcs.push_back(HornRuleExt());
        HornRuleExt& hr = chcs.back();

        if (!normalize(r, hr))
        {
          chcs.pop_back();
          continue;
        }

        Expr body = r->arg(0);
        Expr head = r->arg(1);

        vector<ExprVector> origSrcSymbs;
        ExprSet lin;
        preprocess(body, hr.locVars, origSrcSymbs, hr.srcRelations, lin);
        if (hr.srcRelations.size() == 0)
        {
          if (hasUninterp(body))
          {
            errs () << "Unsupported format\n";
            errs () << "   " << *body << "\n";
            exit (0);
          }
        }

        hr.isFact = hr.srcRelations.empty();

        if (isOpX<FAPP>(head))
        {
          if (head->arg(0)->arity() == 2 && !hr.isFact)
          {
            if (!addFailDecl(head->arg(0)->arg(0)))
            {
              chcs.pop_back();
              continue;
            }
          }
          else
          {
            addDecl(head->arg(0));
          }
          hr.head = head->arg(0);
          hr.dstRelation = hr.head->arg(0);
        }
        else
        {
          if (!isOpX<FALSE>(head)) body = mk<AND>(body, mk<NEG>(head));

          if (!addFailDecl(mk<FALSE>(m_efac)))
          {
            chcs.pop_back();
            continue;
          }
          hr.head = mk<FALSE>(m_efac);
          hr.dstRelation = mk<FALSE>(m_efac);
        }

        hr.isQuery = (hr.dstRelation == failDecl);
        if (removeQuery && hr.isQuery)
        {
          chcs.pop_back();
          continue;
        }
        hr.isInductive = (hr.srcRelations.size() == 1 && hr.srcRelations[0] == hr.dstRelation);
        if (hr.isQuery) qCHCNum = chcs.size() - 1;

        ExprVector allOrigSymbs;
        for (auto & a : origSrcSymbs) for (auto & b : a) allOrigSymbs.push_back(b);
        ExprVector origDstSymbs;
        if (!hr.isQuery)
        {
          for (auto it = head->args_begin()+1, end = head->args_end(); it != end; ++it)
            origDstSymbs.push_back(*it);
        }
        allOrigSymbs.insert(allOrigSymbs.end(), origDstSymbs.begin(), origDstSymbs.end());
        simplBoolReplCnj(allOrigSymbs, lin); // perhaps, not a very important optimization now; consider removing
        hr.body = conjoin(lin, m_efac);

        vector<ExprVector> tmp;
        // we may have several applications of the same predicate symbol in the body:
        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          auto & a = hr.srcRelations[i];
          ExprVector tmp1;
          for (int j = 0; j < i; j++)
          {
            if (hr.srcRelations[i] == hr.srcRelations[j])
            {
              for (int k = 0; k < invVars[a].size(); k++)
              {
                Expr new_name = mkTerm<string> (varname + to_string(++total_var_cnt), m_efac);
                tmp1.push_back(cloneVar(invVars[a][k], new_name));
              }
              break;
            }
          }
          if (tmp1.empty())
          {
            tmp1 = invVars[a];
          }
          tmp.push_back(tmp1);
        }
        hr.assignVarsAndRewrite (origSrcSymbs, tmp,
                                 origDstSymbs, invVars[hr.dstRelation]);

       // hr.body = simpleQE(hr.body, hr.locVars);

        // GF: ideally, hr.locVars should be empty after QE,
        // but the QE procedure is imperfect, so
        ExprVector body_vars;
        expr::filter (hr.body, bind::IsConst(), std::inserter (body_vars, body_vars.begin ()));
        for (auto it = hr.locVars.begin(); it != hr.locVars.end(); )
        {
          if (find(body_vars.begin(), body_vars.end(), *it) == body_vars.end())
            it = hr.locVars.erase(it);
          else ++it;
        }
      }

      for (int i = 0; i < chcs.size(); i++) {
          expr_id[chcs[i].dstRelation] = i;
      }

      prune();

      index_fact_chc = -1;
      // find: index_cycle_chc
      for (int i = 0; i < chcs.size(); i++)
      {
        if (find (chcs[i].srcRelations.begin(), chcs[i].srcRelations.end(),
           chcs[i].dstRelation) != chcs[i].srcRelations.end())
           {
             index_cycle_chc.push_back(i);
             outs () << "cycle found (#" << i << "):\n";
             print(chcs[i]);
           }
      }

      assert(!index_cycle_chc.empty());

      // find fact now:
      for (int i = 0; i < chcs.size(); i++)
      {
        if (chcs[i].isFact && chcs[i].dstRelation == chcs[index_cycle_chc[0]].dstRelation)
         {
           index_fact_chc = i;
           outs () << "fact found (#" << i << "):\n";
           print(chcs[i]);
           break;
         }
      }

      // GF: want to find mutual dependencies here? Then this is incorrect
      // if (index_cycle_chc == -1){
      //   // try to find first cycle ToDo: need to recheck
      //   set<int> tmp_srs;
      //   for (int i = 0; i < chcs.size(); i++) {
      //     if (tmp_srs.find(chcs[i].dstRelation->getId()) != tmp_srs.end()){
      //       index_cycle_chc = i;
      //     }
      //     for(auto srs: chcs[i].srcRelations){
      //       tmp_srs.insert(srs->getId());
      //     }
      //   }
      // }
    }

    vector<vector<int>> cur_batch;
    void findCombs(int num, vector<vector<int>>& res)
    {
      if (num == 1)
      {
        for (int i : index_cycle_chc)
        {
          vector<int> v2 = {i};
          res.push_back(v2);
        }
      }
      else
      {
        findCombs(num - 1, res);
        vector<vector<int>> res2;
        for (auto & v : res)
        {
          for (int i : index_cycle_chc)
          {
            vector<int> v2 = v;
            v2.push_back(i);
            res2.push_back(v2);
          }
        }
        res = res2;
      }
    }

    void clean_cur_batch(){
      while (cur_batch.size() > 0){cur_batch.pop_back();}
    }

    bool mkNewQuery(int cycl_num)
    {
      if (cur_batch.empty())
      {
        outs () << "  cur_batch empt: " << cycl_num << "\n";
        findCombs(cycl_num, cur_batch);
      }

      // outs () << "to copy: " << cy.srcRelations[sum] << "\n";
      chcs.push_back(chcs[index_fact_chc]);
      auto & hr = chcs.back();

      int loc = 0;
      ExprVector newbody;
      ExprVector& prevdst = chcs[index_fact_chc].dstVars;
      Expr prevbody = chcs[index_fact_chc].body;

      for (int i = 0; i < cycl_num; i++)
      {
        auto & cy = chcs[cur_batch.back()[i]];

        int sum = 0, tr = 0;
        for (; sum < cy.srcRelations.size(); sum++)
          if (cy.srcRelations[sum] != cy.dstRelation)
            break;
        for (; tr < cy.srcRelations.size(); tr++)
          if (cy.srcRelations[tr] == cy.dstRelation)
            break;
        ExprVector& cursrc = cy.srcVars[tr];

        // outs () << "\n\ncopy " << i << "\n";

        ExprMap repl1, repl2, repl3;
        for (int k = 0; k < prevdst.size(); k++)
        {
          auto newvar = mkTerm<string> ("_bnd" + to_string(loc), m_efac);
          newvar = cloneVar(prevdst[k], newvar);
          repl1[prevdst[k]] = newvar;
          repl2[cursrc[k]] = newvar;
          loc++;
        }
        for (int k = 0; k < cy.locVars.size(); k++)
        {
          auto newvar = mkTerm<string> ("_loc" + to_string(loc), m_efac);
          newvar = cloneVar(cy.locVars[k], newvar);
          repl2[cy.locVars[k]] = newvar;
          loc++;
        }
        prevbody = replaceAll(prevbody, repl1);
        newbody.push_back(prevbody);
        // pprint(prevbody);
        prevbody = replaceAll(cy.body, repl2);
        prevdst = cy.dstVars;

        hr.srcRelations.push_back(cy.srcRelations[sum]);
        hr.srcVars.push_back(ExprVector());
        ExprVector vars;
        for (auto & v : cy.srcVars[sum])
        {
          auto newvar = mkTerm<string> (varname + to_string(total_var_cnt), m_efac);
          newvar = cloneVar(v, newvar);
          repl3[v] = newvar;
          hr.srcVars.back().push_back(newvar);
          total_var_cnt++;
        }
        prevbody = replaceAll(prevbody, repl3);
      }
      newbody.push_back(prevbody);
      hr.body = conjoin(newbody, m_efac);
      hr.isQuery = 1;
      hr.isInductive = 0;
      hr.isFact = 0;
      hr.dstRelation = failDecl;
      hr.dstVars.clear();

      if (cur_batch.size() > 1){cur_batch.erase(cur_batch.begin());}
      return !cur_batch.empty();
    }

    void print_parse_results(){
      outs() << "chcs \n";
      for (int i = 0; i < chcs.size(); i++){
        outs() << i << " srs: ";
        for (int j = 0; j < chcs[i].srcRelations.size(); j++) {
          outs() << " " <<chcs[i].srcRelations[j]->getId();
        }
        outs() << " dst: " << chcs[i].dstRelation->getId() << " : "
        << chcs[i].dstRelation << " isQuery : " << chcs[i].isQuery << "\n";
      }
      for (auto i : index_cycle_chc)
        outs() << "index_cycle_chc : " << i << "\n";
      int i = 0;
      outs() << "decls \n";
      for (auto d: decls){
        outs() << i << " left: " << d->left()->getId() << " right: " << d->right()->getId() << "\n";
        i++;
      }
      i = 0;
      outs() << "expr_id \n";
      for (auto e: expr_id){
        outs() << i << " first: " << e.first->getId() << " second: " << e.second;
        outs() << "\n";
        i++;
      }
    }


    bool addFailDecl(Expr decl)
    {
      if (failDecl == NULL)
      {
        failDecl = decl;
      }
      else
      {
        if (failDecl != decl)
        {
          //TODO:support
          // errs () << "Multiple queries are not supported\n";
          //exit(0);
          return false;
        }
      }
      return true;
    }

    Expr getPostcondition (int i)
    {
      HornRuleExt& hr = chcs[i];
      ExprSet cnjs;
      ExprSet newCnjs;
      getConj(hr.body, cnjs);
      ExprVector allVars = hr.locVars;
      for (auto & a : hr.srcVars) allVars.insert(allVars.end(), a.begin(), a.end());
      for (auto & a : cnjs)
      {
        if (emptyIntersect(a, allVars)) newCnjs.insert(a);
      }
      return conjoin(newCnjs, m_efac);
    }

    void print()
    {
      outs() << "CHCs:\n";
      for (auto &hr: chcs) print(hr);
    }

    void print(HornRuleExt& hr, bool full = false)
    {
        if (hr.isFact) outs() << "  INIT:\n";
        if (hr.isInductive) outs() << "  TRANSITION RELATION:\n";
        if (hr.isQuery) outs() << "  BAD:\n";

        outs () << "    ";

        for (int i = 0; i < hr.srcRelations.size(); i++)
        {
          outs () << * hr.srcRelations[i];
          if (full)
          {
             outs () << " srcRelations: (";
              for(auto &a: hr.srcVars[i]) outs() << *a << ", ";
                outs () << "\b\b)";
          }
          outs () << " /\\ ";
        }
        outs () << "\b\b\b\b  [arity " << hr.srcRelations.size()<< "] -> " << * hr.dstRelation << "\n";

        if (full)
        {
          if (hr.dstVars.size() > 0)
          {
            outs () << " dstVars: (";
            for(auto &a: hr.dstVars) outs() << *a << ", ";
            outs () << "\b\b)";
          }
          outs() << "\n    body: " << * hr.body << "\n";

          if (hr.locVars.size() > 0)
          {
            outs () << " locVars: (";
            for(auto &a: hr.locVars) outs() << *a << ", ";
            outs () << "\b\b)\n";
          }
        }
    }

  };
}
#endif
