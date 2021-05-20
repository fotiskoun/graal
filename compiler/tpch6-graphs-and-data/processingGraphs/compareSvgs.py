import xml.etree.ElementTree as ET


compLoop = ET.parse('SuperHighTierCompressionTransformationWorked.svg')
CLRoot = compLoop.getroot()

bb = ET.parse('binarySearchInsteadOfShipdate.svg')
BSRoot = bb.getroot()

addNodes = []

removeNodes = []
bsNodesDict = {}
bsNodesList = []
clNodesDict = {}
clNodesList = []
bsEdges = {}
clEdges = {}
addEdges = {}
removeEdges = {}

for CLChild in CLRoot[0]:
  CLClassname = CLChild.attrib.get('class')
  if (CLClassname == 'node'):
    clNodesDict[CLChild[0].text] = CLChild[2].text 
    clNodesList.append(CLChild[2].text)



for child in BSRoot[0]:
  className = child.attrib.get('class')
  if className == 'node':  
    bsNodesDict[child[0].text] = child[2].text
    bsNodesList.append(child[2].text)
      
for n in bsNodesList:
  if n not in clNodesList:
    addNodes.append(n)
    
for n in clNodesList:
  if n not in bsNodesList:
    removeNodes.append(n)  


addNodes.sort()
removeNodes.sort()
#print("Add Nodes\n")
#print(addNodes)
#print("\n\n\n")
#print("Remove Nodes\n")
#print(removeNodes)


for child in BSRoot[0]:
  className = child.attrib.get('class')
  if className == 'edge':
    fromAndTo = child[0].text  
    fromAndTo = fromAndTo.split('->')
    if bsNodesDict[fromAndTo[0]] in bsEdges:
      bsEdges[bsNodesDict[fromAndTo[0]]].append(bsNodesDict[fromAndTo[-1]])
    else:
      bsEdges[bsNodesDict[fromAndTo[0]]] = [bsNodesDict[fromAndTo[-1]]]
    
for child in CLRoot[0]:
  className = child.attrib.get('class')
  if className == 'edge':
    fromAndTo = child[0].text  
    fromAndTo = fromAndTo.split('->')
    if clNodesDict[fromAndTo[0]] in clEdges:
      clEdges[clNodesDict[fromAndTo[0]]].append(clNodesDict[fromAndTo[-1]])
    else:
      clEdges[clNodesDict[fromAndTo[0]]] = [clNodesDict[fromAndTo[-1]]]


print ("\n*************************\n")

for startNode in bsEdges:
  if startNode not in clEdges:
    addEdges[startNode] = bsEdges[startNode]
  else:
    for endNode in bsEdges[startNode]:
      if endNode not in clEdges[startNode]:
        if startNode not in addEdges:
          addEdges[startNode] = [endNode]
        else:
          addEdges[startNode].append(endNode)
        
for edge in addEdges:
  if edge not in clEdges:
    print("Add New Node*******")
  for con in addEdges[edge]:
    print (edge, " --> ", con)
  print("\n")

print("Remove Nodes: ", removeNodes)
for a in addNodes:
  print (a)
print(len(addNodes)) 
#put the nodes in a list to search through them

#create a dict for each file with the node id and the node text
#iterate in both files in the edges and create a dict with the from and to nodes of the edge and translating the node id 
#with the node text and storing the new info in a dict of edges translated
#then print the edges that are not the same
