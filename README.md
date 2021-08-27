# Brown CS 1951x: Formal Proof and Verification, 2021

In this repository, you'll find Lean files for [CS1951x](https://cs.brown.edu/courses/cs1951x).

## Using this repository

This repository is a [Lean project](https://leanprover-community.github.io/install/project.html).
There are some basic steps you should take at the beginning to set it up.
These only need to be done once.
If and when you need to create any new `.lean` files,
create them in the `src` directory of this project,
to ensure that all your expected imports are available.

### Setup

We assume that you have installed:
* `git`
* `lean` (via `elan`)
* `leanproject`
* VSCode and the Lean extension

We will provide details about installing all of these.

We also assume that you have a GitHub account and have 
[added an ssh key to your account](https://docs.github.com/en/github/authenticating-to-github/connecting-to-github-with-ssh).

To set up this project, run:

```bash
leanproject get git@github.com:BrownCS1951x/fpv2021.git
```

When you open VSCode, make sure that you use the **Open Folder** feature
to open the entire `fpv2021` directory,
instead of opening individual files. 
The easiest way to do this is from the command line:
```bash
cd fpv2021
code .
```
But `File -> Open Folder...` works fine too.

### Pulling changes

We will add files to this repository as the course progresses,
and occasionally edit old files. 
We will try very hard to make the homework assignments "read-only":
once they are posted, we will not modify them, and will announce if we do.

You can check whether you have modified any files in the repository with
```bash
git status
```
If you have no modified files, pulling our updates is easy:
```
git pull
```
If you have modifications, you should either commit them:
```
git commit -am "your message here"
git pull
```
or stash them:
```
git stash
git pull
git stash pop
```

Note that modifying files could potentially lead to merge conflicts.
For this reason, especially with the homeworks,
we recommend editing a copy of the files:
```
cp src/homework/homework_1.lean src/homework/homework_1_rob.lean
```

## Contents

`src/lovelib.lean` is a mini-library that we will use for this class.

### Lecture notes

We are following the text *The Hitchhiker's Guide to Logical Verification*.
Corresponding to each chapter of the text, there is a `.lean` file that we will work through in class.
These files are posted here in the `lectures` folder.

### Exercises

We don't have lab sessions for this class, but we do have extra exercise sets.
These are roughly the kinds of problems you would do in a lab.
We'll cover some problems in class, but for the most part, these are practice problems for your benefit.
Feel free to collaborate with your classmates on these.
The solutions are available as well, but of course, try to do the problems without peeking!
Exercises and solutions are available in the `exercises` folder.

### Homework assignments

There is approximately one homework assignment per chapter of the Hitchhiker's Guide.
These will be posted on or before the day of the corresponding lecture, 
and will be due two weeks after that date.
You may discuss problems with your classmates, but the work you submit must be your own.
We recommend the "clean blackboard" method: 
after discussing the problem, erase your blackboard/editor window/etc, 
and write up the solutions individually.
Homeworks will be posted in the `homework` folder.
