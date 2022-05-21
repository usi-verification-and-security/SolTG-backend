#include <list>
#include <map>

using namespace std;

typedef struct {
  vector<int> srs;
  int ds;
} chc_structure;

int entry_value;
map<int, vector<vector<int>>> ds_map_glob;

namespace deep {
  class node {
  public:
    int element;
    vector<node *> children;

    node(int theElement) {
      element = theElement;
      //children = nullptr;
    }

    node(int theElement, node *p) {
      element = theElement;
      //children = nullptr;
    }

    node(int theElement, vector<node *> c) {
      element = theElement;
      for (int i = 0; i < c.size(); i++) {
        add_child(c[i]);
      }
    }

    node(int theElement, vector<int> c) {
      element = theElement;
      for (int i = 0; i < c.size(); i++) {
        node *n = new node{c[i]};
        add_child(n);
      }
    }

    void add_child(node *child) { children.push_back(child); }

    static node* clone(node* n){
      int tmp_e = n->element;
      vector<node *> new_chileds;
      for (auto c : n->children){
        new_chileds.push_back(clone(c));
      }
      node* out = new node{tmp_e, new_chileds};
      return out;
    }

    bool empty(){
      return children.empty();
    }
  };


  class chcTree {
  private:
    node *root;
    vector<node *> non_entry_leaves;
  public:
    chcTree(int r){
      root = new node{r};
    }

    chcTree(node* r){
      root = r;
    }

    chcTree(int parent, vector<int> childrens){
      vector<node *> tmp_nodes;
      for (auto c : childrens){
        auto tmp = new node{c};
        if (c != entry_value){
          non_entry_leaves.push_back(tmp);
        }
        tmp_nodes.push_back(tmp);
      }

      root = new node{parent, childrens};
    }

    ~chcTree() {
      makeEmpty();
    }

    static chcTree* clone(chcTree *t){
      auto new_root = node::clone(t->root);
      auto n_leaves = find_all_non_entry_leaves(new_root); //ToDo: should be improved
      auto n_chcTree = new chcTree(new_root);
      n_chcTree->set_non_entry_leaves(n_leaves);
      return n_chcTree;
    }

    void set_non_entry_leaves(vector<node*> l){
      non_entry_leaves = l;
    }

    static vector<node *> find_all_non_entry_leaves(node* n){ // ToDo: check again, maybe not the best solution
      vector<node *> tmp;
      if(n->children.empty() && n->element != entry_value) {
        tmp.push_back(n);
        return tmp;
      }else{
        for (auto c: n->children){
          for (auto o: find_all_non_entry_leaves(c))
            tmp.push_back(o);
        }
        return tmp;
      }
    }

    const chcTree &operator=(chcTree &&rhs) {
      makeEmpty();
      root = std::move(rhs.root);
      rhs.root = nullptr;
      return *this;
    }

    bool empty() {
      return root->empty();
    }


    void printInOrder()  {
      if (empty()) {
        cout << "tree is emtpy\n";
        return;
      }
      printInOrder(root);
      cout << endl;
    }

    int numOfNodes() const {
      return numOfNodes(root);
    }

    int height() const {
      return height(root);
    }

    void makeEmpty() {
      makeEmpty(root); //? not sure
    }

    bool contains(const int &v) {
      return contains(v, root);
    }

    bool contains(const int &v, node *&t) {
      if (v == root->element) {
        return true;
      }
      return contains(v, root->children);
    }

    bool contains(const int &v, vector<node *> children) {
      //ToDo
      return false;
    }

    void printInOrder(node *t)  {
      if (t == nullptr) { return; }
      cout << t->element << " ";
      for (int i = 0; i < t->children.size(); i++) {
        printInOrder(t->children[i]);
      }
    }

    void printLevelOrder(node *t) const {
      if (t == nullptr) { return; }
      list<node *> tmp_list;
      tmp_list.push_back(t);
      while (!tmp_list.empty()) {
        node *current = tmp_list.front();
        cout << current->element << " ";
        for (int i = 0; i < t->children.size(); i++) {
          tmp_list.push_back(current->children[i]);
        }
        tmp_list.pop_front();
      }
    }

    void makeEmpty(node *&t) {
      if (t != nullptr) {
        for (int i = 0; i < t->children.size(); i++) {
          makeEmpty(t->children[i]);
        }
        delete t;
        t = nullptr;
      }
    }


    int numOfNodes(node *t) const {
      if (t == nullptr) { return 0; }
      int sum = 1;
      for (int i = 0; i < t->children.size(); i++) {
        sum += numOfNodes(t->children[i]);
      }
      return sum;
    }

    int height(node *t) const {
      if (t == nullptr) { return 0; }
      int max_h = 0;
      for (int i = 0; i < t->children.size(); i++) {
        int tmp = height(t->children[i]);
        if (max_h < tmp) {
          max_h = tmp;
        }
      }
      return 1 + max_h;
    }

    bool is_tree_full(){
      return non_entry_leaves.empty();
    }

    void print_map(){
      map<int, vector<vector<int>>>::iterator it;
      for (it = ds_map_glob.begin(); it != ds_map_glob.end(); it++){
        std::cout << it->first;
        vector<vector<int>>::iterator it2;
        for (it2 = it->second.begin(); it2 != it->second.end(); it2++) {
          vector<int>::iterator it3;
          for (it3 = it2->begin(); it3 != it2->end(); it3++) {
            cout << " " << *it3;
          }
        }
        cout << endl;
      }
    }

    vector<vector<vector<int>>> get_all_permutations(){
      vector<vector<vector<int>>> oc;
      vector<vector<int>> out;
      for (int i = 0; i < non_entry_leaves.size(); i++){
        vector<int> tmp;
        out.push_back(tmp);
      }
      get_all_permutations(0, out, oc);
      return oc;
    }

    void get_all_permutations(int index, vector<vector<int>> &out,
                                             vector<vector<vector<int>>> &out_collection){
      if (index >= non_entry_leaves.size()){
        vector<vector<int>> tmp;
        for (int i = 0; i < out.size(); i++) {
          //tmp.push_back(&out[i]);
          tmp.push_back(out[i]);
        }
        //out_collection.push_back(tmp);
        out_collection.push_back(tmp);
        return;
      }
      int el = non_entry_leaves[index]->element;
      int sz = ds_map_glob.find(el)->second.size();
      vector<vector<int>>::iterator it2;
      //for (int i = 0; i < sz; i++) {
      for (it2 = ds_map_glob.find(el)->second.begin(); it2 != ds_map_glob.find(el)->second.end(); it2++) {
        // update current out vector
        out[index] = *it2; //???
        get_all_permutations(index + 1, out, out_collection);
      }
    }

    void extend_non_entry_leaves(vector<vector<int>> new_mutations){
      vector<node *> new_non_entry_leaves;
      for (int i = 0; i < non_entry_leaves.size(); i++){
        auto new_mutation = new_mutations[i];
        vector<node *> tmp_node_list;
        for (auto nm: new_mutation){
          auto n_tmp_node = new node{nm};
          if (nm != entry_value){
            new_non_entry_leaves.push_back(n_tmp_node);
          }
          tmp_node_list.push_back(n_tmp_node);
        }
        non_entry_leaves[i]->children = tmp_node_list;
      }
      non_entry_leaves = new_non_entry_leaves;
    }

  };

  class chcTreeGenerator{
  private:
    int entry;
    int exit_v; //ToDo could be more then one exit point? Should effects only init costructor
    vector<chc_structure> chc_int;
    int current_height;
    vector<chcTree *> trees;
    //vector<chcTree *> fullTrees;
    map<int, vector<vector<int>>> ds_map;
  public:
    chcTreeGenerator(int ep, int ex){
      entry = ep;
      exit_v = ex;
      entry_value = ep;
    }

    void add_chc_int(vector<int> srs_input, int dst_input){
      chc_structure tmp_s = *new chc_structure{srs_input, dst_input};
      chc_int.push_back(tmp_s);
    }

    void create_map(){
        for(auto chc: chc_int){
          if(ds_map.count(chc.ds) > 0){
            ds_map.find(chc.ds)->second.push_back(chc.srs);
            ds_map_glob.find(chc.ds)->second.push_back(chc.srs);
          }else{
            vector<vector<int>> tmp{chc.srs};
            ds_map.insert({chc.ds, tmp});
            ds_map_glob.insert({chc.ds, tmp});

          }
        }
        //ds_map_glob = ds_map;
    }

    void init_tree(){
      auto exit_points = ds_map.find(exit_v);
      for (auto items : exit_points->second){
        chcTree *t = new chcTree(exit_v, items);
        //ToDo: check tree if it if "full" and  add to corresponding list
        trees.push_back(t);
      }
      //chcTree t = new chcTree
    }

    bool is_only_entries(vector<vector<int>> mutation){
      for (int i = 0; i < mutation.size(); i++){
        for (int j = 0; j < mutation[i].size(); j++){
          if (mutation[i][j] != entry){
            return false;
          }
        }
      }
      return true;
    }

    void print_trees(){
      cout << "# of existing trees: " << trees.size() << " existing tree : " << endl;
//      for (auto t: trees){
//        t->printInOrder();
//      }
    }

    vector<chcTree *> getNext(){
      vector<chcTree *> new_trees;
      vector<chcTree *> complete_trees;
      for (int i = 0; i < trees.size(); i++){
        vector<vector<vector<int>>> all_permutations = trees[i]->get_all_permutations();
        for (auto ap : all_permutations){
          //clone tree
          auto nt = chcTree::clone(trees[i]);
          //add values from ap to tree
          nt->extend_non_entry_leaves(ap);
          if (!is_only_entries(ap)){
            // add tree to complete_trees
            new_trees.push_back(nt);
          }else{
            //add tree to new_trees
            complete_trees.push_back(nt);
          }
        }
      }
      trees = new_trees;
      return complete_trees;
    }
  };

}
