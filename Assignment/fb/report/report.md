# REPORT

## Personal Information
- Student Name:Zhengkang Chen
- Student ID:20789905
- WatID:z585chen

## What have been done to compile and run the code
I followed the instructions in the readme file from github because I am using Mac so I didn't counter much issues during the environment setup. I also download the chocolate-doom locally. I created my own script to compile the fuzz with my own parameter and it made my life easier when I tried to increase the coverage.
## What have been done to increase the coverage
First of all, I downloaded different wad files and put it into the seed folder. Secondly, in the fuzz_target.c I trited to call as many function as possible. I also changed the wad file name to increase the converage. As for w_wad.c file, I noticed that there are many line used to throw errors. Thus, what I did is call each function with some invalid inputs and store all the output pf- files.
## What bugs have been found? Can you replay the bug with chocolate-doom, not with the fuzz target?
I didn't find any bugs. 

## Did you manage to compile the game and play it on your local machine (Not inside Docker)?
Yes, I run the game in my own local machine. I download chocolate-doom using brew and run it with the command "chocolate-doom -iwad freedoom2.wad".
