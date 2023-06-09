# 2022.0130
# [Detecting Critical Nodes in Sparse Graphs via "Reduce-Solve-Combine" Memetic Search](https://doi.org/10.1287/ijoc.2022.0130)
This archive is distributed in association with the [INFORMS Journal on Computing](https://pubsonline.informs.org/journal/ijoc) under the MIT License.

## Abstract
This study considers a well-known critical node detection problem that aims to minimize a pairwise connectivity measure of an undirected graph via the removal of a subset of nodes (referred to as critical nodes) subject to a cardinality constraint. Potential applications include epidemic control, emergency response, vulnerability assessment, carbon emission monitoring, network security and drug design. To solve the problem, we present a "reduce-solve-combine" memetic search approach that integrates a problem reduction mechanism into the popular population-based memetic algorithm framework. At each generation, a common pattern mined from two parent solutions is first used to reduce the given problem instance, then the reduced instance is solved by a component-based hybrid neighborhood search that effectively combines an articulation point impact strategy and a node weighting strategy, and finally an offspring solution is produced by combining the mined common pattern and the solution of the reduced instance. Extensive evaluations on 42 real-world and synthetic benchmark instances show the efficacy of the proposed method, which discovers 9 new upper bounds and significantly outperforms the current state-of-the-art algorithms. Investigation of key algorithmic modules additionally discloses the importance of the proposed ideas and strategies. Finally, we demonstrate the generality of the proposed method via its adaptation to solve the node-weighted critical node problem.

## Key words
Critical Node Problem; Memetic Search; Instance Reduction; Reduce-Solve-Combine; Heuristic Search.

## Instances and results
We have considered two classes of CNP benchmark instances, called synthetic instances and realworld instances, which can be found in the two folders "synthetic" and "realworld" of the subdirectory"data" of IRMS, respectively. Also, we provide Weighted CNP benchmark instances, called weighted synthetic instances and weighted realworld instances, which can be found in the two folders "weighted_synthetic" and "weighted_realworld" of the subdirectory"data" of IRMS, respectively. 

The specific illustration of instances can be found in the file "readme.txt"  in each folder for each type of instances. The source files for the method IRMS  is in "src". The method IRMS is coded with C++. Guidances for implementation can be found in the file "readme.txt". Meanwhile, the results output and figures by these methods are available in folder “results”. Each folder also contains a "readme.txt". 

## Paper Entry
Yangming Zhou, Jiaqi Li, Jin-Kao Hao, Fred Glover. ["Detecting Critical Nodes in Sparse Graphs via "Reduce-Solve-Combine" Memetic Search"](https://doi.org/10.1287/ijoc.2022.0130). INFORMS Journal On Computing, 2023.

## Cite
To cite this code, please cite the paper using its DOI and the code itself, using the following DOI.\
DOI:10.1287/ijoc.2022.0130.cd

Below is the BibTex for citing this version of the code.
~~~
@article{detectnode,
  title={Detecting Critical Nodes in Sparse Graphs via "Reduce-Solve-Combine" Memetic Search},
  author={Yangming Zhou and Jiaqi Li and Jin-Kao Hao and Fred Glover},
  publisher={{INFORMS Journal on Computing}},
  year={2023},
  doi={10.1287/ijoc.2022.0130cd},
  note={available for download at https://github.com/INFORMSJoC/2022.0130}
}
~~~
