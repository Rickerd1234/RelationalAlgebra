import { useCallback, useEffect, useState } from 'react';

/**
 * Allow for components to be shown or hidden based on state and localstorage
 * @param Comps list of components to be shown
 * @returns [boolean[], (i: number) => (() => void)]
 */
export default function useVisibleComps(Comps: any[]) {
    // Initial state behavior
    const [visibleComps, setVisibleComps] = useState<boolean[]>(() => {
        const stored = localStorage.getItem('comps');
        try {
            return JSON.parse(stored ?? 'null').map((v: any, i: number) => {
                if (typeof v !== 'boolean') {
                    throw new Error(
                        `TypeError: Comps[${i}] = ${v} - not of type 'boolean'!`
                    );
                }
                return v;
            });
        } catch (err) {
            console.warn('LocalStorage parsing error:\n', err);
            return Comps.map(() => true);
        }
    });

    // Update localstorage when the state changes
    useEffect(() => {
        localStorage.setItem('comps', JSON.stringify(visibleComps));
    }, [visibleComps]);

    // Get toggle function for a specific index
    const getCompToggle = useCallback(
        (i: number) => () =>
            setVisibleComps((oldVisible: boolean[]) => [
                ...oldVisible.map((v: boolean, oi: number) =>
                    i === oi ? !v : v
                ),
            ]),
        [setVisibleComps]
    );

    return [visibleComps, getCompToggle];
}
