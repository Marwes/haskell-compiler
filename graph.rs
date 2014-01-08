use std::vec;
use std::cmp::min;

#[deriving(Eq)]
struct VertexIndex(uint);
#[deriving(Eq)]
struct EdgeIndex(uint);

impl VertexIndex {
    fn get(&self) -> uint { let VertexIndex(v) = *self; v }
}
impl EdgeIndex {
    fn get(&self) -> uint { let EdgeIndex(v) = *self; v }
}

struct Vertex<T> {
    value: T,
    edges: ~[EdgeIndex]
}
struct Edge<T> {
    from: VertexIndex,
    to: VertexIndex
}

pub struct Graph<T> {
    priv edges: ~[Edge<T>],
    priv vertices: ~[Vertex<T>]
}

struct VertexIterator<'a, T> {
    graph: &'a Graph<T>,
    index: uint
}

impl <'a, T> Iterator<&'a Vertex<T>> for VertexIterator<'a, T> {
    fn next(&mut self) -> Option<&'a Vertex<T>> {
        if self.index < self.graph.vertices.len() {
            Some(&self.graph.vertices[self.index])
        }
        else {
            None
        }
    }
}

impl <T> Graph<T> {

    pub fn new() -> Graph<T> {
        Graph { edges: ~[], vertices: ~[] }
    }

    pub fn new_vertex(&mut self, value: T) -> VertexIndex {
        self.vertices.push(Vertex { edges:~[], value: value });
        VertexIndex(self.vertices.len() - 1)
    }

    pub fn connect(&mut self, from: VertexIndex, to: VertexIndex) {
        self.vertices[from.get()].edges.push(EdgeIndex(self.edges.len()));
        self.edges.push(Edge { from: from, to: to });
    }

    pub fn get_vertex<'a>(&'a self, v: VertexIndex) -> &'a Vertex<T> {
        &self.vertices[v.get()]
    }

    pub fn vertices<'a>(&'a self) -> VertexIterator<'a, T> {
        VertexIterator { graph: self, index: 0 }
    }

    pub fn get_edge<'a>(&'a self, edge: EdgeIndex) -> &'a Edge<T> {
        &self.edges[edge.get()]
    }

    pub fn len(&self) -> uint {
        self.vertices.len()
    }
}

pub fn strongly_connected_components<T>(graph: &Graph<T>) -> ~[~[VertexIndex]] {
    
    let mut tarjan = TarjanComponents { graph: graph, index: 1, stack: ~[], connections: ~[],
        valid: vec::from_fn(graph.len(), |_| 0),
        lowlink: vec::from_fn(graph.len(), |_| 0)};
    

    for vert in range(0, graph.len()) {
        if tarjan.valid[vert] == 0 {
            tarjan.strong_connect(VertexIndex(vert));
        }
    }

    tarjan.connections
}

struct TarjanComponents<'a, T>{
    index: uint,
    graph: &'a Graph<T>,
    valid: ~[uint],
    lowlink: ~[uint],
    stack: ~[VertexIndex],
    connections: ~[~[VertexIndex]]
}

impl <'a, T> TarjanComponents<'a, T> {
    fn strong_connect(&mut self, v: VertexIndex) {
        self.valid[v.get()] = self.index;
        self.lowlink[v.get()] = self.index;
        self.index += 1;
        self.stack.push(v);

        for edge_index in self.graph.get_vertex(v).edges.iter() {
            let edge = self.graph.get_edge(*edge_index);
            if self.valid[edge.to.get()] == 0 {
                self.strong_connect(edge.to);
                self.lowlink[v.get()] = min(self.lowlink[v.get()], self.lowlink[edge.to.get()]); 
            }
            else if (self.stack.iter().any(|x| *x == edge.to)) {
                self.lowlink[v.get()] = min(self.lowlink[v.get()], self.valid[edge.to.get()]);
            }
        }

        if self.lowlink[v.get()] == self.valid[v.get()] {
            let mut connected = ~[];
            loop {
                
                let w = self.stack.pop();
                connected.push(w);
                if w == v {
                    break
                }
            }
            self.connections.push(connected);
        }
    }
}


#[test]
fn test_tarjan() {
    let mut graph = Graph::new();
    let v1 = graph.new_vertex(());
    let v2 = graph.new_vertex(());
    let v3 = graph.new_vertex(());
    graph.connect(v1, v2);
    graph.connect(v2, v1);
    graph.connect(v2, v3);
    let connections = strongly_connected_components(&graph);

    assert_eq!(connections.len(), 2);
    assert_eq!(connections[0], ~[v3]);
    assert_eq!(connections[1], ~[v2, v1]);
}

#[test]
fn test_tarjan2() {
    let mut graph = Graph::new();
    let v1 = graph.new_vertex(());
    let v2 = graph.new_vertex(());
    let v3 = graph.new_vertex(());
    let v4 = graph.new_vertex(());
    graph.connect(v1, v2);
    graph.connect(v2, v1);
    graph.connect(v2, v3);
    graph.connect(v3, v4);
    graph.connect(v4, v2);
    let connections = strongly_connected_components(&graph);

    assert_eq!(connections.len(), 1);
    assert_eq!(connections[0], ~[v4, v3, v2, v1]);
}

#[test]
fn test_tarjan3() {
    let mut graph = Graph::new();
    let v1 = graph.new_vertex(());
    let v2 = graph.new_vertex(());
    let v3 = graph.new_vertex(());
    let v4 = graph.new_vertex(());
    let v5 = graph.new_vertex(());
    graph.connect(v1, v2);
    graph.connect(v2, v1);
    graph.connect(v2, v3);
    graph.connect(v3, v4);
    graph.connect(v4, v3);
    graph.connect(v3, v5);
    let connections = strongly_connected_components(&graph);

    assert_eq!(connections.len(), 3);
    assert_eq!(connections[0], ~[v5]);
    assert_eq!(connections[1], ~[v4, v3]);
    assert_eq!(connections[2], ~[v2, v1]);
}
