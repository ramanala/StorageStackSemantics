StorageStackSemantics
=======================
This is a repository to show the flavor of proofs that we discuss in our recent work published at HotOS 2015. Our paper can be found here: https://www.usenix.org/conference/hotos15/workshop-program/presentation/alagappan.

#### What is in this repo?
There is a single Isabelle thoery file which shows how one can model a simple KV store and its operations and prove properties like atomic puts etc.

#### What is Isabelle?
Isabelle is an theorem proving environment. The theory file in this repo is best opened and edited in the jEdit that comes with the Isabelle installer tar. You can download Isabelle from https://isabelle.in.tum.de/.

#### Why do I not see actually symbols like ==> but keywork like RightArrow?
As mentioned in previous question, the file was edited in jEdit and best viewed in the same environment. 

#### How can I run this proof snippets?
If you have successfully installed Isabelle, then just run Isabelle201X from the installation directory - this should open jEdit. Now download this file and open it in jEdit. Now jEdit automatically parses this file and will report if there are any errors. Now you can move your cursor up and down to step through the proof states which is displayed in the output window. 
