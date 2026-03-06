<?xml version="1.0" encoding="UTF-8"?>
<simconf version="2022112801">
  <simulation>
    <title>MTP Test 100 Nodes (1GW + 79AS + 20Dev)</title>
    <randomseed>123456</randomseed>
    <motedelay_us>1000000</motedelay_us>
    <radiomedium>
      org.contikios.cooja.radiomediums.UDGM
      <transmitting_range>150.0</transmitting_range>
      <interference_range>200.0</interference_range>
      <success_ratio_tx>1.0</success_ratio_tx>
      <success_ratio_rx>1.0</success_ratio_rx>
    </radiomedium>
    <events>
      <logoutput>40000</logoutput>
    </events>    <motetype>
      org.contikios.cooja.contikimote.ContikiMoteType
      <description>GW Node</description>
      <source>[CONTIKI_DIR]/examples/myproject/gw-node.c</source>
      <commands>$(MAKE) TARGET=cooja clean
$(MAKE) -j$(CPUS) gw-node.cooja TARGET=cooja</commands>
      <firmware>[CONTIKI_DIR]/examples/myproject/build/cooja/gw-node.cooja</firmware>
      <moteinterface>org.contikios.cooja.interfaces.Position</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.Battery</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiVib</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiMoteID</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiRS232</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiBeeper</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.RimeAddress</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.IPAddress</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiRadio</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiButton</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiPIR</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiClock</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiLED</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiCFS</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.Mote2MoteRelations</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.MoteAttributes</moteinterface>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>1</id>
        </interface_config>
      </mote>    </motetype>
    <motetype>
      org.contikios.cooja.contikimote.ContikiMoteType
      <description>AS Node</description>
      <source>[CONTIKI_DIR]/examples/myproject/as-node.c</source>
      <commands>$(MAKE) TARGET=cooja clean
$(MAKE) -j$(CPUS) as-node.cooja TARGET=cooja</commands>
      <firmware>[CONTIKI_DIR]/examples/myproject/build/cooja/as-node.cooja</firmware>
      <moteinterface>org.contikios.cooja.interfaces.Position</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.Battery</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiVib</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiMoteID</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiRS232</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiBeeper</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.RimeAddress</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.IPAddress</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiRadio</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiButton</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiPIR</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiClock</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiLED</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiCFS</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.Mote2MoteRelations</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.MoteAttributes</moteinterface>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>2</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>3</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>4</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>5</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>6</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>7</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>8</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>9</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="0" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>10</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>11</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>12</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>13</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>14</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>15</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>16</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>17</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>18</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>19</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="30" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>20</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>21</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>22</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>23</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>24</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>25</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>26</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>27</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>28</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>29</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="60" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>30</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>31</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>32</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>33</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>34</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>35</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>36</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>37</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>38</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>39</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="90" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>40</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>41</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>42</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>43</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>44</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>45</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>46</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>47</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>48</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>49</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="120" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>50</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>51</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>52</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>53</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>54</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>55</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>56</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>57</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>58</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>59</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="150" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>60</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>61</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>62</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>63</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>64</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>65</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>66</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>67</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>68</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>69</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="180" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>70</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>71</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>72</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>73</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>74</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>75</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>76</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>77</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>78</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>79</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="210" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>80</id>
        </interface_config>
      </mote>    </motetype>
    <motetype>
      org.contikios.cooja.contikimote.ContikiMoteType
      <description>Device Node</description>
      <source>[CONTIKI_DIR]/examples/myproject/device-node.c</source>
      <commands>$(MAKE) TARGET=cooja clean
$(MAKE) -j$(CPUS) device-node.cooja TARGET=cooja</commands>
      <firmware>[CONTIKI_DIR]/examples/myproject/build/cooja/device-node.cooja</firmware>
      <moteinterface>org.contikios.cooja.interfaces.Position</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.Battery</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiVib</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiMoteID</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiRS232</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiBeeper</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.RimeAddress</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.IPAddress</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiRadio</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiButton</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiPIR</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiClock</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiLED</moteinterface>
      <moteinterface>org.contikios.cooja.contikimote.interfaces.ContikiCFS</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.Mote2MoteRelations</moteinterface>
      <moteinterface>org.contikios.cooja.interfaces.MoteAttributes</moteinterface>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>81</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>82</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>83</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>84</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>85</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>86</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>87</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>88</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>89</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="240" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>90</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="0" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>91</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="30" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>92</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="60" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>93</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="90" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>94</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="120" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>95</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="150" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>96</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="180" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>97</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="210" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>98</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="240" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>99</id>
        </interface_config>
      </mote>      <mote>
        <interface_config>
          org.contikios.cooja.interfaces.Position
          <pos x="270" y="270" />
        </interface_config>
        <interface_config>
          org.contikios.cooja.contikimote.interfaces.ContikiMoteID
          <id>100</id>
        </interface_config>
      </mote>    </motetype>
  </simulation>
  <plugin>
    org.contikios.cooja.plugins.LogListener
    <plugin_config>
      <filter />
      <formatted_time />
      <coloring />
    </plugin_config>
    <bounds x="400" y="1" height="400" width="800" z="1" />
  </plugin>
  <plugin>
    org.contikios.cooja.plugins.ScriptRunner
    <plugin_config>
      <script>
TIMEOUT(1800000, log.testOK());
while(true) {
  log.log(time + " " + id + " " + msg + "\n");
  YIELD();
}
      </script>
      <active>true</active>
    </plugin_config>
    <bounds x="0" y="600" height="300" width="600" z="3" />
  </plugin>
</simconf>
