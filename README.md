# Prolog_Convex_Hull

convex_hull_algorithms.pl has the prolog code for 4 convex hull algorithms namely, convex closure method, graham scan method, jarvis march method and the quickhull method.
To obtain the solutions for convex hull using the convex closure method, the final predicate is convex_hull/6. It takes the dimensions and constraints and outputs the results; the details of this method have been mentioned in the report.
For the remaining three algorithms, you can modify the points.txt file to input any number of points in the format of points(serial number, x-coordinaate, y-coordinate). 
Simply call the predicates grahaam_scan/3, jarvis_march/3, quickhull/3 to get the convex hull.
