<h1 align="center">
  🧑‍🎓Bachelor Project🧑‍🎓
</h1>
<h4 align="center"> Disjoint Set implementation </h4>

## Topic
We commonly find various code implementations online, which we need to use in our projects. However, there is a problem with how to know that the code does what it has to do correctly and at the same time does nothing extra. For these purposes, it is possible to use the ACSL annotation language (in the case of C programming language, specifically the Frama-C framework), whose task is formally proving that the code is correct. The aim of this bachelor thesis is: 
* Research the Frama-C framework. 
* Research the possible Disjoint-Set data structure implementation. 
* Implement some of them in C programming language.
* Compare the performance of our implementations.

## Framework
### Frama-C
Frama-C is framework for performing analysis of the source code written in C, C++, ...
Framework contains a lot of plugins for various analysis, from generating annotations about possible overflow of the variables to verification of the concurent programs.
