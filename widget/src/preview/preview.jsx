import React from 'react';
import ReactDOM from 'react-dom';
import useVisibleComps from './useVisibleComps';
import Widget1 from '../Widget1';
import Widget2 from '../Widget2';

const Comps = [Widget1, Widget2];

function Main() {
    const [visibleComps, getCompToggle] = useVisibleComps(Comps);

    return (
        <div>
            <h1>Lean Widget Preview</h1>
            {Comps.map((Component, i) => (
                <div key={`c-${Component.name}`} style={{ padding: '10px' }}>
                    <button
                        onClick={getCompToggle(i)}
                        children={`${visibleComps[i] ? 'Hide' : 'Show'} ${Component.name}`}
                    />
                    {visibleComps[i] ? <Component /> : null}
                </div>
            ))}
        </div>
    );
}

ReactDOM.createRoot(document.getElementById('root')).render(<Main />);
